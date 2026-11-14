from __future__ import annotations  # fixes 'type object is not subscriptable' on Python 3.8

import json
import math
import os
import random
import sqlite3
import threading
import time
import traceback
import urllib.request
import webbrowser
from collections import deque
from contextlib import contextmanager
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from urllib.parse import urlparse


DB_PATH = os.getenv("ASTRO_DB", "astra_spatial.db")
MODEL_FILE = os.getenv("ASTRO_MODEL", "astronaut.glb")
DB_LOCK = threading.Lock()

LAST: dict[str, dict] = {}
PPG: dict[str, dict] = {}
OVERRIDES: dict[str, dict] = {}

RAMP_TAU_S = float(os.getenv("ASTRO_RAMP_TAU", "30"))
TRUE_STATE: dict[str, list] = {}

SCENARIOS = ("Nominal", "Solar Storm", "Suit Leak", "Thermal Spike")


CAREER_LIMIT_MSV = 600.0
INCIDENT_LOG = os.getenv("ASTRO_INCIDENT_LOG", "astra_incidents.jsonl")

LEVEL_RANK = {"watch": 1, "warning": 2, "critical": 3}
RANK_NAME = {0: "ok", 1: "watch", 2: "warning", 3: "critical"}
SEVERITY_RANK = {v: k for k, v in RANK_NAME.items()}

LABELS = {
    "hr": ("Heart rate", "BPM"),
    "spo2": ("Blood oxygen (SpO2)", "%"),
    "temp": ("Skin temperature", "C"),
    "psi": ("Suit pressure", "PSI"),
    "neutron": ("Neutron dose rate", "uSv/h"),
}

RISK_MODEL = {
    "hr": (64.0, 115.0),
    "spo2": (98.6, 92.0),
    "temp": (36.6, 37.8),
    "psi": (4.30, 3.5),
    "neutron": (6.2, 25.0),
}
PRIOR_STD = {"hr": 6.0, "spo2": 1.0, "temp": 0.25, "psi": 0.08, "neutron": 2.5}
PLAUSIBLE = {  # outside this range the reading is a sensor fault, not a patient problem
    "hr": (20.0, 240.0),
    "spo2": (50.0, 100.5),
    "temp": (30.0, 45.0),
    "psi": (-0.5, 6.0),
    "neutron": (0.0, 5000.0),
}
PRIORITY = [
    "low_pressure", "hypoxia", "radiation", "hyperthermia", "hypothermia",
    "bradycardia", "tachycardia", "dose", "signal", "sensor", "telemetry",
]
STATE_OF = {
    "low_pressure": "Suit Leak / Hypoxia", "hypoxia": "Suit Leak / Hypoxia",
    "radiation": "Radiation Exposure", "dose": "Radiation Dose Limit",
    "hyperthermia": "Heat Stress", "hypothermia": "Hypothermia",
    "tachycardia": "Cardiac Stress", "bradycardia": "Bradycardia",
    "signal": "PPG Signal Lost", "sensor": "Sensor Fault", "telemetry": "Telemetry Lost",
}
EXPECTED = {  # vitals that normally move together for a given condition
    "Suit Leak / Hypoxia": {"psi", "spo2", "hr"},
    "Heat Stress": {"temp", "hr"},
    "Radiation Exposure": {"neutron", "hr"},
}
PLAYBOOK = {
    "Suit Leak / Hypoxia": (
        "Falling suit pressure with dropping blood oxygen and compensatory tachycardia points to a "
        "pressure-garment breach or a PLSS oxygen supply fault.",
        [
            "Press 'O2 Pressure Purge' to raise suit O2 and restore pressure",
            "Locate and seal the breach (gloves, wrist rings, helmet seal, hose connections)",
            "Abort EVA and return to the airlock if pressure does not recover within 60 s",
        ],
    ),
    "Radiation Exposure": (
        "A sudden rise in neutron dose rate is consistent with a solar particle event or a shielding failure.",
        [
            "Press 'Deploy Shielding' and move to the storm shelter",
            "Terminate EVA and return to the airlock",
            "Log the accumulated dose and notify the flight surgeon",
        ],
    ),
    "Heat Stress": (
        "Rising skin temperature with an elevated heart rate is consistent with a cooling-garment (LCVG) "
        "shortfall or overexertion.",
        [
            "Press 'Max LCVG Cooling'",
            "Stop strenuous work and rest until temperature falls below 37.5 C",
            "Hydrate and abort EVA if temperature keeps rising",
        ],
    ),
    "Cardiac Stress": (
        "Sustained high heart rate without another cause suggests overexertion, anxiety or early cardiac strain.",
        ["Stop activity and rest", "Check cooling and O2 settings", "Ask flight surgeon to review the ECG/PPG trace"],
    ),
    "Bradycardia": (
        "Abnormally slow heart rate can indicate a cardiac rhythm problem or sensor error.",
        ["Verify with a second sensor", "Contact the flight surgeon", "Stop activity and monitor"],
    ),
    "Hypothermia": (
        "Low skin temperature indicates the cooling garment is over-cooling or insulation has failed.",
        ["Reduce LCVG cooling", "Check suit insulation", "Return to the airlock if it keeps falling"],
    ),
    "Radiation Dose Limit": (
        "The astronaut's cumulative dose is close to or beyond the career limit.",
        ["Restrict further EVA time", "Notify the flight surgeon / mission control"],
    ),
    "PPG Signal Lost": (
        "The pulse sensor has no usable signal, so heart rate and SpO2 shown are NOT real measurements.",
        ["Re-seat the ring/finger sensor", "Use a backup sensor or voice check-in"],
    ),
    "Sensor Fault": (
        "One or more readings are physically implausible, which indicates a failed or disconnected sensor.",
        ["Cross-check with redundant sensors", "Do a voice check-in with the crew member"],
    ),
    "Telemetry Lost": (
        "No data is arriving from the suit. The crew member's health is unknown.",
        ["Contact the crew member by voice", "Check the suit comms / sensor link"],
    ),
}


def _say(msg: str):
    try:
        print(msg, flush=True)
    except UnicodeEncodeError:
        print(msg.encode("ascii", "replace").decode("ascii"), flush=True)


def _iso(ts: float) -> str:
    return time.strftime("%Y-%m-%d %H:%M:%S", time.localtime(ts))


def _median3(xs):
    ys = sorted(xs[-3:])
    return ys[len(ys) // 2]


def _slope(points):
    n = len(points)
    if n < 2:
        return 0.0
    mt = sum(t for t, _ in points) / n
    my = sum(y for _, y in points) / n
    den = sum((t - mt) ** 2 for t, _ in points)
    return 0.0 if den < 1e-9 else sum((t - mt) * (y - my) for t, y in points) / den


def _finding(code, vital, level, title, detail, action, value=None):
    return {
        "code": code, "vital": vital, "level": level, "title": title,
        "detail": detail, "action": action, "value": value,
    }


def invalid_channels(v: dict) -> list:
    bad = []
    for k, (lo, hi) in PLAUSIBLE.items():
        x = v.get(k)
        if (
            not isinstance(x, (int, float)) or isinstance(x, bool)
            or math.isnan(x) or math.isinf(x) or not (lo <= x <= hi)
        ):
            bad.append(k)
    return bad


def assess(c: dict, skip=()) -> list:
    """Clinical rules: turns one (smoothed) set of vitals into a list of findings."""
    f = []
    hr, spo2, temp, psi, neu = c["hr"], c["spo2"], c["temp"], c["psi"], c["neutron"]
    cum = c.get("cumulative_msv", 0.0) or 0.0

    if "spo2" not in skip:
        if spo2 < 88:
            f.append(_finding("hypoxia", "spo2", "critical", "Severe hypoxia", f"SpO2 {spo2:.1f}% (normal 95-100%)",
                              "Raise suit O2 now (O2 Pressure Purge) and prepare to abort EVA", spo2))
        elif spo2 < 92:
            f.append(_finding("hypoxia", "spo2", "warning", "Hypoxia", f"SpO2 {spo2:.1f}% (normal 95-100%)",
                              "Increase suit O2 flow and reduce exertion", spo2))
        elif spo2 < 95:
            f.append(_finding("hypoxia", "spo2", "watch", "Low blood oxygen", f"SpO2 {spo2:.1f}%",
                              "Monitor closely and check the suit O2 supply", spo2))

    if psi < 3.0:
        f.append(_finding("low_pressure", "psi", "critical", "Suit pressure critically low",
                          f"{psi:.2f} PSI (nominal 4.30)", "Run O2 Pressure Purge, find the breach, return to airlock", psi))
    elif psi < 3.5:
        f.append(_finding("low_pressure", "psi", "warning", "Suit pressure dropping",
                          f"{psi:.2f} PSI (nominal 4.30)", "Run O2 Pressure Purge and inspect seals", psi))
    elif psi < 4.0:
        f.append(_finding("low_pressure", "psi", "watch", "Suit pressure below nominal",
                          f"{psi:.2f} PSI (nominal 4.30)", "Inspect seals and monitor", psi))

    if "hr" not in skip:
        if hr > 140:
            f.append(_finding("tachycardia", "hr", "critical", "Severe tachycardia", f"{hr:.0f} BPM (resting ~64)",
                              "Stop all activity; check cooling, O2 and pressure", hr))
        elif hr > 115:
            f.append(_finding("tachycardia", "hr", "warning", "Tachycardia", f"{hr:.0f} BPM (resting ~64)",
                              "Reduce workload and check cooling/O2", hr))
        elif hr > 100:
            f.append(_finding("tachycardia", "hr", "watch", "Elevated heart rate", f"{hr:.0f} BPM (resting ~64)",
                              "Ease off and monitor", hr))
        elif hr < 40:
            f.append(_finding("bradycardia", "hr", "critical", "Severe bradycardia", f"{hr:.0f} BPM",
                              "Contact the flight surgeon immediately", hr))
        elif hr < 50:
            f.append(_finding("bradycardia", "hr", "warning", "Bradycardia", f"{hr:.0f} BPM",
                              "Verify with a second sensor and notify the flight surgeon", hr))

    if temp >= 38.5:
        f.append(_finding("hyperthermia", "temp", "critical", "Severe hyperthermia", f"Skin {temp:.1f} C (normal ~36.6)",
                          "Max LCVG cooling now and abort EVA", temp))
    elif temp > 37.8:
        f.append(_finding("hyperthermia", "temp", "warning", "Hyperthermia", f"Skin {temp:.1f} C (normal ~36.6)",
                          "Max LCVG cooling and rest", temp))
    elif temp > 37.5:
        f.append(_finding("hyperthermia", "temp", "watch", "Rising skin temperature", f"Skin {temp:.1f} C",
                          "Increase cooling and monitor", temp))
    elif temp <= 35.0:
        f.append(_finding("hypothermia", "temp", "critical", "Severe hypothermia", f"Skin {temp:.1f} C",
                          "Reduce cooling and return to the airlock", temp))
    elif temp < 35.5:
        f.append(_finding("hypothermia", "temp", "warning", "Hypothermia", f"Skin {temp:.1f} C",
                          "Reduce LCVG cooling", temp))
    elif temp < 36.0:
        f.append(_finding("hypothermia", "temp", "watch", "Low skin temperature", f"Skin {temp:.1f} C",
                          "Check cooling settings", temp))

    if neu >= 100:
        f.append(_finding("radiation", "neutron", "critical", "Severe radiation exposure",
                          f"{neu:.1f} uSv/h (normal ~6)", "Deploy shielding and shelter immediately", neu))
    elif neu >= 25:
        f.append(_finding("radiation", "neutron", "warning", "High radiation exposure",
                          f"{neu:.1f} uSv/h (normal ~6)", "Deploy shielding and prepare to shelter", neu))
    elif neu >= 15:
        f.append(_finding("radiation", "neutron", "watch", "Elevated radiation",
                          f"{neu:.1f} uSv/h (normal ~6)", "Monitor space-weather alerts", neu))

    pct = cum / CAREER_LIMIT_MSV * 100.0
    if pct >= 100:
        f.append(_finding("dose", "dose", "critical", "Career dose limit reached",
                          f"{cum:.1f} of {CAREER_LIMIT_MSV:.0f} mSv", "No further EVA; notify flight surgeon", cum))
    elif pct >= 85:
        f.append(_finding("dose", "dose", "warning", "Approaching career dose limit",
                          f"{cum:.1f} of {CAREER_LIMIT_MSV:.0f} mSv ({pct:.0f}%)", "Limit further EVA time", cum))
    elif pct >= 70:
        f.append(_finding("dose", "dose", "watch", "Career dose rising",
                          f"{cum:.1f} of {CAREER_LIMIT_MSV:.0f} mSv ({pct:.0f}%)", "Plan remaining EVA carefully", cum))
    return f


def render_report(inc: dict) -> str:
    bar = "=" * 64
    L = [bar, "ASTRA // CREW HEALTH INCIDENT REPORT", bar]
    L.append(f"Report ID     : {inc['id']}")
    L.append(f"Crew member   : {inc['name']} ({inc['astronaut_id']})")
    L.append(f"Status        : {inc['status']}")
    L.append(f"Severity      : {inc['severity'].upper()} (peak: {inc['peak_severity'].upper()})")
    L.append(f"Condition     : {inc['state']}")
    L.append(f"Opened        : {inc['opened_at']}")
    L.append(f"Closed        : {inc['closed_at'] or '-'}   (duration {inc['duration_s']} s)")
    L += ["", "SUMMARY", f"  {inc['headline']}", "", "FINDINGS"]
    for f in inc["findings"]:
        L.append(f"  [{f['level'].upper():8}] {f['title']}: {f['detail']}")
        L.append(f"             -> {f['action']}")
    L += ["", f"{'VITALS':24}{'AT DETECTION':>14}{'LATEST':>12}"]
    for k, (label, unit) in LABELS.items():
        if k in inc["snapshot"]:
            L.append(f"  {label + ' (' + unit + ')':22}{inc['detected'].get(k, '-'):>14}{inc['snapshot'][k]:>12}")
    if "cumulative_msv" in inc["snapshot"]:
        L.append(f"  {'Career dose (mSv)':22}{inc['detected'].get('cumulative_msv', '-'):>14}"
                 f"{inc['snapshot']['cumulative_msv']:>12}")
    if inc["extremes"]:
        L += ["", "WORST VALUES DURING INCIDENT"]
        for k, v in inc["extremes"].items():
            L.append(f"  {LABELS[k][0]:22}: {v} {LABELS[k][1]}")
    if inc["trend"]:
        L += ["", f"TRENDS (at worst point, predicted {AstraAI.HORIZON_S} s ahead)"]
        for k, t in inc["trend"].items():
            L.append(f"  {LABELS[k][0]:22}: {t['slope_per_min']:+.2f} {LABELS[k][1]}/min -> {t['predicted']}")
    L += ["", "PROBABLE CAUSE", f"  {inc['probable_cause']}", "", "RECOMMENDED ACTIONS"]
    for i, a in enumerate(inc["recommended_actions"], 1):
        L.append(f"  {i}. {a}")
    L += ["", "TIMELINE"]
    for e in inc["timeline"]:
        L.append(f"  {e['t']}  {e['event']}")
    L.append(bar)
    return "\n".join(L)


class _Track:
    def __init__(self):
        self.valid = deque(maxlen=60)  # (ts, vitals) of plausible samples
        self.last_push = 0.0
        self.name = None
        self.baseline = {k: m[0] for k, m in RISK_MODEL.items()}
        self.bad_signal = 0
        self.stale = False
        self.last_error = None
        self.incident = None
        self.last_incident = None
        self.ok_streak = 0
        self.result = {"status": "loading"}


class AstraAI:
    HORIZON_S = 30       # how far ahead the early-warning looks
    WARMUP_N = 10        # samples before trend/risk is trusted
    WINDOW_N = 30        # samples used for trend regression
    STALE_S = 5.0        # no data for this long = telemetry lost
    RESOLVE_AFTER_S = 8  # seconds of healthy data before an incident is closed
    DAMP = 0.6           

    def __init__(self, app_ramp_tau: float = 30.0, log_path: str | None = None):
        self.app_ramp_tau = app_ramp_tau
        self.log_path = log_path or INCIDENT_LOG
        self._lock = threading.RLock()
        self._tracks: dict[str, _Track] = {}
        self._reports: deque = deque(maxlen=200)
        self._counter = 0
        self._started = False
        self._warned: dict[str, float] = {}

    # ---------------------------------------------------------------- public API
    def start(self):
        with self._lock:
            if self._started:
                return
            self._started = True
        threading.Thread(target=self._watchdog, daemon=True).start()

    def push(self, aid: str, vitals: dict):
        now = time.time()
        with self._lock:
            tr = self._tracks.get(aid)
            if tr is None:
                tr = self._tracks[aid] = _Track()
            tr.last_push, tr.stale, tr.last_error = now, False, None
            if vitals.get("name"):
                tr.name = vitals["name"]
            try:
                res = self._analyse(aid, tr, vitals, now)
                self._update_incident(aid, tr, res, now)
                res["health"]["incident_id"] = tr.incident["id"] if tr.incident else None
                tr.result = res
            except Exception as e:  # noqa: BLE001
                tr.result = {"status": "error", "reason": f"AI analysis failed: {type(e).__name__}: {e}"}
                self._warn_once(f"analyse-{aid}", f"[ASTRA][ERROR] AI analysis failed for {aid}: {e!r}")

    def note_error(self, aid: str, message: str):
        """Called by the simulator when a step fails, so the report can say why telemetry stopped."""
        with self._lock:
            tr = self._tracks.get(aid)
            if tr is not None:
                tr.last_error = message

    def get(self, aid: str) -> dict:
        with self._lock:
            tr = self._tracks.get(aid)
            return dict(tr.result) if tr else {"status": "loading"}

    def info(self) -> dict:
        with self._lock:
            open_n = sum(1 for t in self._tracks.values() if t.incident)
            return {
                "status": "ok", "engine": "ASTRA health AI (clinical rules + trend prediction + anomaly check)",
                "horizon_s": self.HORIZON_S, "crew_tracked": len(self._tracks),
                "open_incidents": open_n, "total_incidents": self._counter, "log_file": self.log_path,
            }

    def crew(self) -> list:
        with self._lock:
            out = []
            for aid, tr in self._tracks.items():
                h = (tr.result or {}).get("health")
                if not h:
                    continue
                out.append({
                    "id": aid, "name": tr.name or aid, "severity": h["severity"],
                    "rank": SEVERITY_RANK[h["severity"]], "score": h["score"], "state": h["state"],
                    "headline": h["headline"], "incident_id": h.get("incident_id"),
                })
            return out

    def reports(self, limit: int = 50) -> list:
        with self._lock:
            items = list(self._reports)[-limit:][::-1]
            return json.loads(json.dumps([self._public(i) for i in items]))

    def latest_report(self, aid: str):
        with self._lock:
            tr = self._tracks.get(aid)
            inc = tr.last_incident if tr else None
            if inc is None:
                return None
            pub = json.loads(json.dumps(self._public(inc)))
        pub["text"] = render_report(pub)
        return pub

    # ------------------------------------------------------------------ analysis
    @staticmethod
    def _public(inc: dict) -> dict:
        return {k: v for k, v in inc.items() if not k.startswith("_")}

    def _warn_once(self, key: str, msg: str, every: float = 15.0):
        now = time.time()
        if now - self._warned.get(key, 0.0) >= every:
            self._warned[key] = now
            _say(msg)

    @staticmethod
    def _smooth(tr: _Track) -> dict:
        vals = [s for _, s in list(tr.valid)[-3:]]
        cur = {k: _median3([s[k] for s in vals]) for k in RISK_MODEL}
        cur["cumulative_msv"] = vals[-1]["cumulative_msv"]
        return cur

    def _analyse(self, aid, tr, v, now):
        extra = []
        bad = invalid_channels(v)
        if bad:
            labels = ", ".join(LABELS[k][0] for k in bad)
            extra.append(_finding(
                "sensor", "sensor", "warning", "Sensor fault",
                f"{labels}: reading missing or physically implausible",
                "Cross-check with redundant sensors; treat these values as unreliable"))
        else:
            sample = {k: float(v[k]) for k in RISK_MODEL}
            sample["cumulative_msv"] = float(v.get("cumulative_msv") or 0.0)
            tr.valid.append((now, sample))

        # PPG quality: analyze_ppg() falls back to fake 'healthy' numbers when it finds no pulse
        tr.bad_signal = 0 if v.get("signal_ok", True) else tr.bad_signal + 1
        skip = set()
        if tr.bad_signal >= 3:
            skip |= {"hr", "spo2"}
            extra.append(_finding(
                "signal", "hr", "warning", "PPG signal lost",
                f"no pulse detected for {tr.bad_signal} s - heart rate and SpO2 are not real measurements",
                "Re-seat the ring/finger sensor or use a backup sensor"))

        n = len(tr.valid)
        if n == 0:
            return self._build(aid, tr, extra, None, {}, 0.0, [], 0)

        cur = self._smooth(tr)
        findings = assess(cur, skip) + extra

        # trend + early-warning risk
        trend, risk = {}, 0.0
        if n >= self.WARMUP_N:
            series = list(tr.valid)[-self.WINDOW_N:]
            for k, (nom, lim) in RISK_MODEL.items():
                if k in skip:
                    continue
                ys = [s[k] for _, s in series]
                sm = [_median3(ys[max(0, i - 2): i + 1]) for i in range(len(ys))]
                slope = _slope([(t, y) for (t, _), y in zip(series, sm)])
                lo, hi = PLAUSIBLE[k]
                pred = min(hi, max(lo, cur[k] + slope * self.HORIZON_S * self.DAMP))
                frac = (pred - nom) / (lim - nom)  # 1.0 == predicted to be at the alert limit
                rv = min(1.0, max(0.0, (frac - 0.25) / 0.75))
                trend[k] = {"slope_per_min": round(slope * 60, 2), "predicted": round(pred, 2), "risk": round(rv, 2)}
                risk = max(risk, rv)

        # anomaly vs. this astronaut's own baseline
        anomalies = [
            k for k in RISK_MODEL
            if k not in skip and abs(cur[k] - tr.baseline[k]) / PRIOR_STD[k] >= 4.0
        ]
        if not findings and not anomalies:  # learn what 'normal' looks like for this person
            for k in RISK_MODEL:
                tr.baseline[k] += 0.02 * (cur[k] - tr.baseline[k])

        return self._build(aid, tr, findings, cur, trend, risk, anomalies, n)

    def _build(self, aid, tr, findings, cur, trend, risk, anomalies, n):
        findings = sorted(findings, key=lambda f: (-LEVEL_RANK[f["level"]], PRIORITY.index(f["code"])))
        rank = LEVEL_RANK[findings[0]["level"]] if findings else 0
        primary = findings[0] if findings else None
        state = STATE_OF[primary["code"]] if primary else "Nominal"

        if rank >= 2:
            risk = 1.0
        elif rank == 1:
            risk = max(risk, 0.45)

        if primary:
            expected = EXPECTED.get(state, set())
            corr = sum(1 for f in findings[1:] if f["vital"] in expected and f["vital"] != primary["vital"])
            conf = min(0.99, 0.55 + 0.12 * rank + 0.08 * corr)
        else:
            conf = max(0.5, 0.99 - 0.5 * risk)
        level = "warn" if risk >= 0.6 else ("watch" if (risk >= 0.3 or anomalies) else "ok")

        tv = max(trend, key=lambda k: trend[k]["risk"]) if trend else None
        if primary:
            headline = f"{primary['title']} - {primary['detail']}"
        elif tv and trend[tv]["risk"] >= 0.3:
            headline = f"{LABELS[tv][0]} drifting toward its alert limit"
        else:
            headline = "All vitals normal" if cur else "Waiting for telemetry"

        # ---- feedback for the astronaut / flight surgeon
        fb = [f"{f['title']}: {f['detail']}. Action: {f['action']}." for f in findings]
        for k in sorted(trend, key=lambda k: -trend[k]["risk"]):
            t = trend[k]
            if t["risk"] >= 0.3 and not any(f["vital"] == k for f in findings):
                label, unit = LABELS[k]
                way = "rising" if t["slope_per_min"] > 0 else "falling"
                fb.append(f"{label} is {way} ({t['slope_per_min']:+.1f} {unit}/min); predicted {t['predicted']} {unit} "
                          f"in {self.HORIZON_S} s.")
        if anomalies and not findings:
            fb.append("Unusual reading compared with this crew member's baseline: "
                      + ", ".join(LABELS[k][0] for k in anomalies) + ".")
        if cur and rank == 0:
            fb.insert(0, f"All monitored vitals are within the normal range (HR {cur['hr']:.0f} BPM, "
                         f"SpO2 {cur['spo2']:.1f}%, skin {cur['temp']:.1f} C, suit {cur['psi']:.2f} PSI).")
            pct = cur["cumulative_msv"] / CAREER_LIMIT_MSV * 100
            fb.append(f"Career radiation dose: {cur['cumulative_msv']:.1f} of {CAREER_LIMIT_MSV:.0f} mSv ({pct:.0f}%).")

        # ---- recommended actions
        actions = []
        if rank >= 2 and state in PLAYBOOK:
            actions += PLAYBOOK[state][1]
        for f in findings:
            if f["action"] not in actions:
                actions.append(f["action"])
        if not actions:
            actions = ["Continue nominal EVA operations"]
        actions = actions[:5]

        # ---- health score 0-100
        pens = sorted((6 if f["level"] == "watch" else 20 if f["level"] == "warning" else 40 for f in findings),
                      reverse=True)
        pen = (pens[0] + 0.5 * sum(pens[1:])) if pens else 0.0
        score = int(max(0, min(100, round(100 - pen - 10 * risk))))

        health = {
            "severity": RANK_NAME[rank], "score": score, "state": state, "headline": headline,
            "feedback": fb, "actions": actions, "findings": findings, "error": rank >= 2,
            "name": tr.name or aid, "incident_id": None,
        }
        return {
            "status": "ok" if n >= self.WARMUP_N else "warming_up",
            "have": n, "need": self.WARMUP_N,
            "state": state, "confidence": round(conf, 2), "risk": round(risk, 2),
            "horizon_s": self.HORIZON_S, "anomaly": bool(anomalies), "anomaly_vitals": anomalies,
            "level": level, "trend": trend,
            "vitals": {k: round(x, 2) for k, x in cur.items()} if cur else {},
            "health": health,
        }

    # ----------------------------------------------------------------- incidents
    def _update_incident(self, aid, tr, res, now):
        h = res["health"]
        rank = SEVERITY_RANK[h["severity"]]
        inc = tr.incident
        if rank >= 2:
            tr.ok_streak = 0
            if inc is None:
                inc = self._open_incident(aid, tr, res, now)
                tr.incident = tr.last_incident = inc
                self._reports.append(inc)
                _say(f"[ASTRA][ERROR] {inc['name']}: {inc['headline']}  (report {inc['id']})")
                self._log(inc, "opened")
            else:
                self._refresh_incident(inc, res, rank, now)
        elif inc is not None:
            tr.ok_streak += 1
            inc["duration_s"] = int(now - inc["_opened_ts"])
            if tr.ok_streak >= self.RESOLVE_AFTER_S:
                inc["status"] = "RESOLVED"
                inc["closed_at"] = _iso(now)
                inc["severity"] = "ok"
                inc["timeline"].append({"t": _iso(now), "event": "Vitals back in normal range - incident resolved"})
                _say(f"[ASTRA][INFO] {inc['name']}: incident {inc['id']} resolved after {inc['duration_s']} s")
                self._log(inc, "resolved")
                tr.incident = None

    def _open_incident(self, aid, tr, res, now):
        h = res["health"]
        self._counter += 1
        state = h["state"]
        cause = PLAYBOOK.get(state, ("Cause could not be determined automatically.", []))[0]
        inc = {
            "id": f"INC-{time.strftime('%Y%m%d', time.localtime(now))}-{self._counter:04d}",
            "astronaut_id": aid, "name": tr.name or aid, "status": "OPEN",
            "severity": h["severity"], "peak_severity": h["severity"], "state": state,
            "headline": h["headline"], "opened_at": _iso(now), "closed_at": None, "duration_s": 0,
            "findings": list(h["findings"]), "snapshot": dict(res["vitals"]),
            "detected": dict(res["vitals"]), "extremes": {},
            "trend": dict(res["trend"]), "probable_cause": cause,
            "recommended_actions": list(h["actions"]),
            "timeline": [{"t": _iso(now), "event": f"Incident opened ({h['severity']}): {h['headline']}"}],
            "_peak_rank": SEVERITY_RANK[h["severity"]], "_opened_ts": now,
        }
        self._track_extremes(inc, res["vitals"])
        return inc

    @staticmethod
    def _track_extremes(inc, vit):
        for k, fn in (("hr", max), ("temp", max), ("neutron", max), ("spo2", min), ("psi", min)):
            x = vit.get(k)
            if x is not None:
                inc["extremes"][k] = x if k not in inc["extremes"] else fn(inc["extremes"][k], x)

    def _refresh_incident(self, inc, res, rank, now):
        h = res["health"]
        inc["duration_s"] = int(now - inc["_opened_ts"])
        inc["severity"] = h["severity"]
        inc["snapshot"] = dict(res["vitals"])
        self._track_extremes(inc, res["vitals"])
        if rank >= inc["_peak_rank"]:  # the report describes the WORST moment, not the recovery
            inc["headline"], inc["findings"] = h["headline"], list(h["findings"])
            inc["recommended_actions"] = list(h["actions"])
            if res["trend"]:
                inc["trend"] = dict(res["trend"])
            if h["state"] != inc["state"]:
                inc["state"] = h["state"]
                inc["probable_cause"] = PLAYBOOK.get(h["state"], (inc["probable_cause"], []))[0]
                inc["timeline"].append({"t": _iso(now), "event": f"Condition changed to {h['state']}: {h['headline']}"})
        if rank > inc["_peak_rank"]:
            inc["_peak_rank"], inc["peak_severity"] = rank, h["severity"]
            inc["timeline"].append({"t": _iso(now), "event": f"ESCALATED to {h['severity'].upper()}: {h['headline']}"})
            _say(f"[ASTRA][ERROR] {inc['name']}: escalated to {h['severity'].upper()} - {h['headline']} "
                 f"(report {inc['id']})")
            self._log(inc, "escalated")
        del inc["timeline"][:-50]

    def _log(self, inc, event):
        try:
            with open(self.log_path, "a", encoding="utf-8") as f:
                f.write(json.dumps({"event": event, "report": self._public(inc)}, ensure_ascii=False) + "\n")
        except Exception as e:  # noqa: BLE001
            self._warn_once("log", f"[ASTRA][WARN] could not write incident log {self.log_path}: {e!r}")

    # ------------------------------------------------------------------ watchdog
    def _watchdog(self):
        while True:
            time.sleep(1.0)
            try:
                now = time.time()
                with self._lock:
                    for aid, tr in self._tracks.items():
                        if tr.last_push and now - tr.last_push > self.STALE_S:
                            tr.stale = True
                            res = self._stale_result(aid, tr, now)
                            self._update_incident(aid, tr, res, now)
                            res["health"]["incident_id"] = tr.incident["id"] if tr.incident else None
                            tr.result = res
            except Exception as e:  # noqa: BLE001
                self._warn_once("watchdog", f"[ASTRA][ERROR] AI watchdog error: {e!r}")

    def _stale_result(self, aid, tr, now):
        detail = f"no telemetry for {now - tr.last_push:.0f} s"
        if tr.last_error:
            detail += f" (last simulator error: {tr.last_error})"
        fnd = [_finding("telemetry", "telemetry", "critical", "Telemetry lost", detail,
                        "Contact the crew member by voice and check the suit comms link")]
        cur = self._smooth(tr) if tr.valid else None
        return self._build(aid, tr, fnd, cur, {}, 1.0, [], len(tr.valid))


AI = None
AI_ERR = "disabled (ASTRO_AI=0)"
if os.getenv("ASTRO_AI", "1") != "0":
    try:
        AI = AstraAI(app_ramp_tau=RAMP_TAU_S)
    except Exception as _e:  # noqa: BLE001
        AI_ERR = f"AI health monitor failed to start: {_e}"

# Public domain / CC-BY official NASA & Khronos high-detail spacesuit GLB mirrors
GLB_SOURCES = [
    "https://raw.githubusercontent.com/google/model-viewer/master/packages/shared-assets/models/Astronaut.glb",
    "https://modelviewer.dev/shared-assets/models/Astronaut.glb",
]


def ensure_glb_asset():
    """Downloads the high-detail photorealistic NASA Astronaut.glb locally if not already present."""
    if os.path.isfile(MODEL_FILE) and os.path.getsize(MODEL_FILE) > 100_000:
        return
    for url in GLB_SOURCES:
        try:
            req = urllib.request.Request(url, headers={"User-Agent": "ASTRA-EVA-OS/1.0"})
            with urllib.request.urlopen(req, timeout=8) as resp:
                data = resp.read()
                if len(data) > 100_000:
                    with open(MODEL_FILE, "wb") as f:
                        f.write(data)
                    print(f"[ASTRA] Cached high-detail 3D spacesuit asset -> {MODEL_FILE} ({len(data)//1024} KB)")
                    return
        except Exception:
            continue


@contextmanager
def db():
    with DB_LOCK:
        con = sqlite3.connect(DB_PATH, check_same_thread=False)
        con.row_factory = sqlite3.Row
        try:
            yield con
            con.commit()
        finally:
            con.close()


def init_db():
    with db() as con:
        con.executescript(
            """
            CREATE TABLE IF NOT EXISTS astronauts (
                id TEXT PRIMARY KEY,
                name TEXT,
                scenario TEXT DEFAULT 'Nominal',
                cumulative_msv REAL DEFAULT 142.5
            );
            """
        )
        if con.execute("SELECT COUNT(*) FROM astronauts").fetchone()[0] == 0:
            con.executemany(
                "INSERT INTO astronauts (id, name, scenario, cumulative_msv) VALUES (?, ?, ?, ?)",
                [
                    ("amira", "Cdr. Amira Hassan", "Nominal", 184.2),
                    ("lukas", "FE. Lukas Berg", "Nominal", 112.8),
                    ("yuki", "MS. Yuki Tanaka", "Nominal", 96.4),
                ],
            )


def get_overrides(aid: str) -> dict:
    return OVERRIDES.setdefault(
        aid, {"o2_boost": False, "cool_max": False, "shield_shelter": False}
    )


def analyze_ppg(red: list[float], ir: list[float], fs: int = 100):
    n = len(ir)
    win_s, win_f = max(3, int(fs * 0.6)), max(2, int(fs * 0.08))
    half_s, half_f = win_s // 2, win_f // 2

    detrended = [
        ir[i] - sum(ir[max(0, i - half_s) : min(n, i + half_s + 1)]) / (min(n, i + half_s + 1) - max(0, i - half_s))
        for i in range(n)
    ]
    filtered = [
        round(
            sum(detrended[max(0, i - half_f) : min(n, i + half_f + 1)])
            / (min(n, i + half_f + 1) - max(0, i - half_f)),
            2,
        )
        for i in range(n)
    ]

    mean_f = sum(filtered) / n
    std_f = math.sqrt(sum((x - mean_f) ** 2 for x in filtered) / n)
    if std_f < 1e-6:
        return 64.0, 98.6, filtered, False  # no usable pulse: values are placeholders

    min_dist = int(fs * 0.32)
    thresh = 0.45 * std_f
    peaks = []
    for i in range(1, n - 1):
        if filtered[i] > thresh and filtered[i] >= filtered[i - 1] and filtered[i] > filtered[i + 1]:
            if not peaks or (i - peaks[-1]) >= min_dist:
                peaks.append(i)

    if len(peaks) < 2:
        return 64.0, 98.6, filtered, False  # no usable pulse: values are placeholders

    rr_ms = [(peaks[i + 1] - peaks[i]) / fs * 1000.0 for i in range(len(peaks) - 1)]
    hr = max(42.0, min(205.0, 60000.0 / (sum(rr_ms) / len(rr_ms))))

    dc_r, dc_i = max(1.0, sum(red) / n), max(1.0, sum(ir) / n)
    ac_r = math.sqrt(sum((x - dc_r) ** 2 for x in red) / n)
    ac_i = math.sqrt(sum((x - dc_i) ** 2 for x in ir) / n)
    r_val = (ac_r / dc_r) / max(1e-6, (ac_i / dc_i))
    spo2 = max(72.0, min(99.8, 110.0 - 25.0 * r_val))
    return hr, spo2, filtered, True


def ease_state(aid: str, target):
    """First-order lag toward the scenario target (radiation reacts ~5x faster than physiology)."""
    cur = TRUE_STATE.get(aid)
    if cur is None or RAMP_TAU_S <= 0:
        cur = list(target)
    else:
        a = 1.0 - math.exp(-1.0 / RAMP_TAU_S)
        a_n = 1.0 - math.exp(-1.0 / max(1.0, RAMP_TAU_S / 5.0))
        cur = [c + (t - c) * (a_n if i == 4 else a) for i, (c, t) in enumerate(zip(cur, target))]
    TRUE_STATE[aid] = cur
    return tuple(cur)


def step_simulation(aid: str, scenario: str):
    ov = get_overrides(aid)
    targets = {
        "Nominal": (64.0, 98.6, 36.6, 4.30, 6.2),
        "Solar Storm": (134.0, 96.2, 37.3, 4.30, 148.0),
        "Suit Leak": (154.0, 86.0, 36.8, 2.75, 12.0),
        "Thermal Spike": (142.0, 96.5, 38.6, 4.30, 8.5),
    }
    hr_t, spo2_t, temp_t, psi_t, neut_t = targets.get(scenario, targets["Nominal"])

    if ov.get("shield_shelter"):
        neut_t, hr_t = 5.4, min(hr_t, 76.0)
    if ov.get("o2_boost"):
        spo2_t, psi_t, hr_t = 99.1, 4.30, min(hr_t, 78.0)
    if ov.get("cool_max"):
        temp_t, hr_t = 36.5, min(hr_t, 76.0)

    hr_t, spo2_t, temp_t, psi_t, neut_t = ease_state(aid, (hr_t, spo2_t, temp_t, psi_t, neut_t))

    hr_now = hr_t + random.gauss(0, 1.0)
    spo2_now = max(72.0, min(99.8, spo2_t + random.gauss(0, 0.16)))
    temp_now = temp_t + random.gauss(0, 0.04)
    psi_now = psi_t + random.gauss(0, 0.01)
    neut_now = max(0.5, neut_t + random.gauss(0, neut_t * 0.03))

    fs, n = 100, 260
    freq = hr_now / 60.0
    r_ratio = max(0.4, (110.0 - spo2_now) / 25.0)
    ir, red = [], []
    for i in range(n):
        t = i / fs
        pulse = math.sin(2 * math.pi * freq * t) + 0.35 * math.sin(4 * math.pi * freq * t - 0.6)
        ir.append(10000.0 + 180.0 * pulse + random.gauss(0, 5.5))
        red.append(10000.0 + (180.0 * r_ratio) * pulse + random.gauss(0, 5.5))

    hr_est, spo2_est, filtered, sig_ok = analyze_ppg(red, ir, fs)

    with db() as con:
        row = con.execute("SELECT name, cumulative_msv FROM astronauts WHERE id=?", (aid,)).fetchone()
        cum_msv = float(row["cumulative_msv"] if row else 142.5) + (neut_now / 1000.0) * (15.0 / 3600.0)
        con.execute("UPDATE astronauts SET cumulative_msv=? WHERE id=?", (cum_msv, aid))
        crew_name = row["name"] if row else aid

    LAST[aid] = {
        "name": crew_name,
        "signal_ok": bool(sig_ok),
        "scenario": scenario,
        "hr": round(hr_est, 1),
        "spo2": round(spo2_est, 1),
        "temp": round(temp_now, 1),
        "psi": round(psi_now, 2),
        "neutron": round(neut_now, 1),
        "cumulative_msv": round(cum_msv, 2),
    }
    PPG[aid] = filtered
    if AI is not None:
        try:
            AI.push(aid, LAST[aid])
        except Exception:  # noqa: BLE001  the AI must never be able to stall the simulation
            pass


def worker():
    time.sleep(0.2)
    last_err: dict = {}
    while True:
        try:
            with db() as con:
                crew = [dict(r) for r in con.execute("SELECT id, scenario FROM astronauts")]
        except Exception as e:  # noqa: BLE001
            print(f"[ASTRA][ERROR] database read failed: {e!r}", flush=True)
            time.sleep(2.0)
            continue
        for m in crew:
            try:
                step_simulation(m["id"], m["scenario"])
            except Exception as e:  # noqa: BLE001  one bad step must not kill the telemetry thread
                msg = f"{type(e).__name__}: {e}"
                if AI is not None:
                    AI.note_error(m["id"], msg)
                key = (m["id"], type(e).__name__)
                if time.time() - last_err.get(key, 0.0) > 10:
                    last_err[key] = time.time()
                    print(f"[ASTRA][ERROR] simulation step failed for {m['id']}: {msg}", flush=True)
                    traceback.print_exc()
        time.sleep(1.0)


# ============================================================================
# 2. HTTP SERVER
# ============================================================================
class Handler(BaseHTTPRequestHandler):
    def log_message(self, fmt, *args):
        pass

    def _json(self, data, status=200):
        raw = json.dumps(data).encode("utf-8")
        self.send_response(status)
        self.send_header("Content-Type", "application/json")
        self.send_header("Cache-Control", "no-store")
        self.send_header("Content-Length", str(len(raw)))
        self.end_headers()
        self.wfile.write(raw)

    def _body(self):
        ln = int(self.headers.get("Content-Length", 0))
        return json.loads(self.rfile.read(ln).decode("utf-8")) if ln else {}

    def _guard(self, fn):
        try:
            fn()
        except (BrokenPipeError, ConnectionResetError, ConnectionAbortedError):
            pass
        except ValueError as e:  # bad JSON body etc.
            try:
                self._json({"error": f"bad request: {e}"}, 400)
            except Exception:  # noqa: BLE001
                pass
        except Exception as e:  # noqa: BLE001
            print(f"[ASTRA][ERROR] HTTP {self.command} {self.path}: {e!r}", flush=True)
            traceback.print_exc()
            try:
                self._json({"error": f"{type(e).__name__}: {e}"}, 500)
            except Exception:  # noqa: BLE001
                pass

    def do_GET(self):
        self._guard(self._get)

    def do_PUT(self):
        self._guard(self._put)

    def _get(self):
        path = urlparse(self.path).path
        if path == "/":
            raw = HTML_UI.encode("utf-8")
            self.send_response(200)
            self.send_header("Content-Type", "text/html; charset=utf-8")
            self.send_header("Cache-Control", "no-store")
            self.send_header("Content-Length", str(len(raw)))
            self.end_headers()
            self.wfile.write(raw)
            return

        if path == "/models/astronaut.glb":
            if os.path.isfile(MODEL_FILE) and os.path.getsize(MODEL_FILE) > 100_000:
                with open(MODEL_FILE, "rb") as f:
                    raw = f.read()
                self.send_response(200)
                self.send_header("Content-Type", "model/gltf-binary")
                self.send_header("Cache-Control", "no-store")
                self.send_header("Content-Length", str(len(raw)))
                self.end_headers()
                self.wfile.write(raw)
                return
            return self._json({"error": "No local astronaut.glb found"}, 404)

        if path.startswith("/api/state/"):
            aid = path.split("/")[-1]
            ai = AI.get(aid) if AI is not None else {"status": "unavailable", "reason": AI_ERR}
            return self._json({"vitals": LAST.get(aid), "ppg": PPG.get(aid, []), "ai": ai})

        if path == "/api/ai/crew":
            return self._json({"crew": AI.crew() if AI is not None else []})

        if path == "/api/ai/reports":
            return self._json({"reports": AI.reports() if AI is not None else []})

        if path.startswith("/api/ai/report/"):
            rep = AI.latest_report(path.split("/")[-1]) if AI is not None else None
            return self._json({"report": rep})

        if path == "/api/ai/status":
            return self._json(AI.info() if AI is not None else {"status": "unavailable", "reason": AI_ERR})

        self._json({"error": "not found"}, 404)

    def _put(self):
        parts = urlparse(self.path).path.strip("/").split("/")
        if len(parts) == 4 and parts[:2] == ["api", "crew"] and parts[3] == "scenario":
            aid = parts[2]
            sc = self._body().get("scenario", "Nominal")
            if sc not in SCENARIOS:
                return self._json({"error": f"unknown scenario {sc!r}", "allowed": list(SCENARIOS)}, 400)
            with db() as con:
                con.execute("UPDATE astronauts SET scenario=? WHERE id=?", (sc, aid))
            if sc == "Nominal":
                OVERRIDES[aid] = {"o2_boost": False, "cool_max": False, "shield_shelter": False}
            return self._json({"ok": True, "scenario": sc})

        if len(parts) == 4 and parts[:2] == ["api", "crew"] and parts[3] == "overrides":
            aid = parts[2]
            body = self._body()
            ov = get_overrides(aid)
            for k in ("o2_boost", "cool_max", "shield_shelter"):
                if k in body:
                    ov[k] = bool(body[k])
            with db() as con:
                row = con.execute("SELECT scenario FROM astronauts WHERE id=?", (aid,)).fetchone()
                sc = row["scenario"] if row else "Nominal"
                resolved = (
                    (sc == "Solar Storm" and ov.get("shield_shelter"))
                    or (sc == "Suit Leak" and ov.get("o2_boost"))
                    or (sc == "Thermal Spike" and ov.get("cool_max"))
                )
                if resolved:
                    con.execute("UPDATE astronauts SET scenario='Nominal' WHERE id=?", (aid,))
                    OVERRIDES[aid] = {"o2_boost": False, "cool_max": False, "shield_shelter": False}
            return self._json({"ok": True, "resolved": resolved})

        self._json({"error": "not found"}, 404)


# ============================================================================
# 3. PHOTOREALISTIC PBR ASTRONAUT + PRESERVED ASTRA // ORBITAL EVA OS UI
# ============================================================================
HTML_UI = """<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="UTF-8">
<meta name="viewport" content="width=device-width, initial-scale=1.0">
<title>ASTRA // ORBITAL EVA OS</title>
<link rel="preconnect" href="https://fonts.googleapis.com">
<link href="https://fonts.googleapis.com/css2?family=JetBrains+Mono:wght@500;700&family=Space+Grotesk:wght@400;500;600;700&display=swap" rel="stylesheet">
<script src="https://cdnjs.cloudflare.com/ajax/libs/three.js/r128/three.min.js"></script>
<script src="https://cdn.jsdelivr.net/npm/three@0.128.0/examples/js/loaders/GLTFLoader.js"></script>
<script src="https://cdn.jsdelivr.net/npm/three@0.128.0/examples/js/environments/RoomEnvironment.js"></script>
<style>
  :root {
    --bg-deep: #02040A;
    --glass: rgba(10, 16, 30, 0.65);
    --glass-strong: rgba(10, 16, 30, 0.85);
    --stroke: rgba(148, 163, 184, 0.18);
    --text-main: #F1F5F9;
    --text-dim: #94A3B8;
    --mint: #2DD4BF;
    --amber: #FBBF24;
    --coral: #FB7185;
  }

  * {
    box-sizing: border-box;
    margin: 0;
    padding: 0;
    font-family: 'Space Grotesk', -apple-system, sans-serif;
  }

  body {
    background: radial-gradient(circle at 50% 45%, #070D1D 0%, var(--bg-deep) 85%);
    color: var(--text-main);
    width: 100vw;
    height: 100vh;
    overflow: hidden;
    position: relative;
  }

  #stage3d {
    position: fixed;
    inset: 0;
    width: 100%;
    height: 100%;
    display: block;
    cursor: grab;
    z-index: 1;
  }
  #stage3d:active { cursor: grabbing; }

  .top-bar {
    position: fixed;
    top: 20px;
    left: 24px;
    right: 24px;
    z-index: 10;
    display: flex;
    justify-content: space-between;
    align-items: center;
    pointer-events: none;
  }

  .capsule {
    pointer-events: auto;
    background: var(--glass);
    backdrop-filter: blur(18px);
    -webkit-backdrop-filter: blur(18px);
    border: 1px solid var(--stroke);
    border-radius: 99px;
    padding: 8px 18px;
    display: flex;
    align-items: center;
    gap: 12px;
    box-shadow: 0 12px 32px rgba(0, 0, 0, 0.6);
  }

  .status-dot {
    width: 9px;
    height: 9px;
    border-radius: 50%;
    background: var(--mint);
    box-shadow: 0 0 12px var(--mint);
    transition: all 0.25s;
  }
  .status-dot.warn { background: var(--amber); box-shadow: 0 0 14px var(--amber); }
  .status-dot.crit { background: var(--coral); box-shadow: 0 0 16px var(--coral); }

  .brand-name { font-weight: 700; font-size: 14px; letter-spacing: 0.04em; }
  .brand-sub { font-size: 12px; color: var(--text-dim); }

  .crew-select {
    background: transparent;
    border: none;
    color: var(--text-main);
    font-weight: 600;
    font-size: 13px;
    cursor: pointer;
    outline: none;
  }
  .crew-select option { background: #090E1A; color: #F1F5F9; }

  .mono {
    font-family: 'JetBrains Mono', monospace;
    font-size: 12px;
    color: var(--mint);
  }

  .hud-wing {
    position: fixed;
    top: 50%;
    transform: translateY(-50%);
    z-index: 10;
    display: flex;
    flex-direction: column;
    gap: 14px;
    pointer-events: none;
  }
  .hud-wing.left { left: 28px; }
  .hud-wing.right { right: 28px; align-items: flex-end; }

  .hud-node {
    pointer-events: auto;
    background: var(--glass);
    backdrop-filter: blur(18px);
    -webkit-backdrop-filter: blur(18px);
    border: 1px solid var(--stroke);
    border-radius: 18px;
    padding: 14px 18px;
    width: 215px;
    transition: all 0.25s ease;
    box-shadow: 0 10px 28px rgba(0, 0, 0, 0.5);
  }
  .hud-node.alert {
    border-color: rgba(251, 113, 133, 0.75);
    background: rgba(66, 18, 32, 0.76);
    box-shadow: 0 0 28px rgba(251, 113, 133, 0.3);
  }
  .node-kicker {
    font-size: 10.5px;
    font-weight: 600;
    letter-spacing: 0.08em;
    text-transform: uppercase;
    color: var(--text-dim);
    display: flex;
    justify-content: space-between;
  }
  .node-value {
    font-family: 'JetBrains Mono', monospace;
    font-size: 24px;
    font-weight: 700;
    margin-top: 4px;
    color: var(--text-main);
  }
  .hud-node.alert .node-value { color: var(--coral); }
  .node-foot { font-size: 11px; color: var(--text-dim); margin-top: 3px; }

  .ring-orb {
    pointer-events: auto;
    background: var(--glass);
    backdrop-filter: blur(18px);
    border: 1px solid var(--stroke);
    border-radius: 18px;
    padding: 12px;
    width: 215px;
    text-align: center;
    transition: all 0.25s;
  }
  .ring-orb.vibe {
    border-color: var(--coral);
    animation: orbShake 0.14s infinite;
  }
  @keyframes orbShake {
    0%, 100% { transform: translate(0, 0); }
    25% { transform: translate(-2px, 1px); }
    75% { transform: translate(2px, -1px); }
  }
  #ringMini { width: 140px; height: 82px; display: block; margin: 0 auto; }

  .dock-wrap {
    position: fixed;
    bottom: 22px;
    left: 50%;
    transform: translateX(-50%);
    z-index: 20;
    display: flex;
    flex-direction: column;
    align-items: center;
    gap: 10px;
    width: max-content;
    max-width: 95vw;
  }

  .ai-toast {
    background: var(--glass-strong);
    backdrop-filter: blur(20px);
    border: 1px solid rgba(45, 212, 191, 0.35);
    border-radius: 99px;
    padding: 8px 20px;
    font-size: 13px;
    font-weight: 500;
    color: var(--text-main);
    display: flex;
    align-items: center;
    gap: 10px;
    box-shadow: 0 10px 30px rgba(0, 0, 0, 0.65);
    transition: all 0.25s;
  }
  .ai-toast.warn { border-color: var(--amber); background: rgba(54, 38, 12, 0.9); }
  .ai-toast.crit { border-color: var(--coral); background: rgba(68, 16, 29, 0.92); }
  .toast-badge {
    font-family: 'JetBrains Mono', monospace;
    font-size: 10.5px;
    font-weight: 700;
    padding: 2px 8px;
    border-radius: 99px;
    background: rgba(45, 212, 191, 0.16);
    color: var(--mint);
  }
  .ai-toast.warn .toast-badge { background: rgba(251, 191, 36, 0.2); color: var(--amber); }
  .ai-toast.crit .toast-badge { background: rgba(251, 113, 133, 0.22); color: var(--coral); }

  .dock {
    background: var(--glass-strong);
    backdrop-filter: blur(22px);
    -webkit-backdrop-filter: blur(22px);
    border: 1px solid var(--stroke);
    border-radius: 22px;
    padding: 8px 10px;
    display: flex;
    align-items: center;
    gap: 8px;
    box-shadow: 0 18px 45px rgba(0, 0, 0, 0.75);
    flex-wrap: wrap;
    justify-content: center;
  }

  .dock-group { display: flex; align-items: center; gap: 5px; }
  .dock-label {
    font-size: 10px;
    font-weight: 700;
    letter-spacing: 0.08em;
    text-transform: uppercase;
    color: var(--text-dim);
    padding: 0 8px;
  }
  .dock-divider { width: 1px; height: 26px; background: var(--stroke); margin: 0 4px; }

  .pill-btn {
    border: 1px solid transparent;
    background: rgba(255, 255, 255, 0.05);
    color: var(--text-dim);
    padding: 8px 13px;
    border-radius: 13px;
    font-size: 12px;
    font-weight: 600;
    cursor: pointer;
    transition: all 0.18s ease;
  }
  .pill-btn:hover { color: var(--text-main); background: rgba(255, 255, 255, 0.11); }
  .pill-btn.active {
    background: rgba(251, 113, 133, 0.2);
    border-color: rgba(251, 113, 133, 0.55);
    color: #FFE4E6;
  }
  .pill-btn.nom.active {
    background: rgba(45, 212, 191, 0.18);
    border-color: rgba(45, 212, 191, 0.5);
    color: var(--mint);
  }

  .fix-btn {
    border: 1px solid var(--stroke);
    background: rgba(255, 255, 255, 0.03);
    color: var(--text-dim);
    padding: 8px 14px;
    border-radius: 13px;
    font-size: 12px;
    font-weight: 600;
    opacity: 0.42;
    cursor: not-allowed;
    transition: all 0.2s ease;
  }
  .fix-btn.ready {
    opacity: 1;
    cursor: pointer;
    background: linear-gradient(135deg, rgba(45, 212, 191, 0.24), rgba(56, 189, 248, 0.24));
    border-color: var(--mint);
    color: #FFFFFF;
    box-shadow: 0 0 20px rgba(45, 212, 191, 0.35);
    animation: pulseMint 1.3s infinite;
  }
  .fix-btn.ready:hover {
    background: var(--mint);
    color: #062825;
    transform: translateY(-1px);
  }
  @keyframes pulseMint {
    50% { box-shadow: 0 0 28px rgba(45, 212, 191, 0.6); }
  }
  /* AI co-pilot panel */
  .ai-bar { height: 4px; border-radius: 3px; background: rgba(148, 163, 184, 0.18); margin-top: 7px; overflow: hidden; }
  .ai-bar-fill { height: 100%; width: 0%; background: var(--mint); transition: width 0.4s ease, background 0.4s ease; }
  .hud-node.ai-watch { border-color: var(--amber); }
  .hud-node.ai-warn { border-color: var(--coral); }

  /* Crew health AI */
  .hud-node.health-watch { border-color: var(--amber); }
  .hud-node.health-warn { border-color: var(--amber); background: rgba(54, 38, 12, 0.80); }
  .hud-node.health-crit {
    border-color: rgba(251, 113, 133, 0.75);
    background: rgba(66, 18, 32, 0.78);
    box-shadow: 0 0 28px rgba(251, 113, 133, 0.3);
  }
  .hud-node.health-warn .node-value { color: var(--amber); }
  .hud-node.health-crit .node-value { color: var(--coral); }
  .health-action { color: var(--text-main); opacity: 0.85; }
  .rpt-btn {
    margin-top: 8px; width: 100%; padding: 7px 10px; border-radius: 11px; cursor: pointer;
    border: 1px solid var(--coral); background: rgba(251, 113, 133, 0.18);
    color: #FFE4E6; font-size: 11.5px; font-weight: 700; letter-spacing: 0.03em;
  }
  .rpt-btn:hover { background: var(--coral); color: #2A0A12; }

  .err-banner {
    position: fixed; top: 78px; left: 50%; transform: translateX(-50%); z-index: 15;
    display: none; align-items: center; gap: 12px; max-width: min(900px, 92vw);
    padding: 9px 12px 9px 18px; border-radius: 99px; font-size: 13px; font-weight: 600;
    backdrop-filter: blur(18px); -webkit-backdrop-filter: blur(18px);
    box-shadow: 0 12px 34px rgba(0, 0, 0, 0.7);
  }
  .err-banner.show { display: flex; }
  .err-banner.crit { background: rgba(68, 16, 29, 0.94); border: 1px solid var(--coral); color: #FFE4E6; animation: errPulse 1.2s infinite; }
  .err-banner.warn { background: rgba(54, 38, 12, 0.94); border: 1px solid var(--amber); color: #FEF3C7; }
  @keyframes errPulse { 50% { box-shadow: 0 0 34px rgba(251, 113, 133, 0.55); } }
  .err-banner button {
    border: 1px solid currentColor; background: transparent; color: inherit; border-radius: 99px;
    padding: 5px 13px; font-size: 11.5px; font-weight: 700; cursor: pointer; white-space: nowrap;
  }
  .err-banner button:hover { background: rgba(255, 255, 255, 0.14); }

  .modal {
    position: fixed; inset: 0; z-index: 40; display: none; align-items: center; justify-content: center;
    background: rgba(2, 4, 10, 0.72); backdrop-filter: blur(6px);
  }
  .modal.show { display: flex; }
  .modal-card {
    width: min(720px, 94vw); max-height: 86vh; display: flex; flex-direction: column;
    background: var(--glass-strong); border: 1px solid var(--stroke); border-radius: 20px;
    box-shadow: 0 24px 70px rgba(0, 0, 0, 0.85); overflow: hidden;
  }
  .modal-head {
    display: flex; justify-content: space-between; align-items: center; padding: 14px 18px;
    border-bottom: 1px solid var(--stroke); font-weight: 700; font-size: 14px;
  }
  .modal-head button, .modal-foot button {
    border: 1px solid var(--stroke); background: rgba(255, 255, 255, 0.06); color: var(--text-main);
    border-radius: 11px; padding: 7px 14px; font-size: 12px; font-weight: 600; cursor: pointer;
  }
  .modal-head button:hover, .modal-foot button:hover { background: rgba(255, 255, 255, 0.14); }
  #rptBody {
    margin: 0; padding: 16px 18px; overflow: auto; font-family: 'JetBrains Mono', monospace;
    font-size: 12px; line-height: 1.55; color: var(--text-main); white-space: pre-wrap;
  }
  .modal-foot { display: flex; gap: 8px; justify-content: flex-end; padding: 12px 18px; border-top: 1px solid var(--stroke); }
</style>
</head>
<body>

  <canvas id="stage3d"></canvas>

  <header class="top-bar">
    <div class="capsule">
      <span id="statusDot" class="status-dot"></span>
      <span class="brand-name">ASTRA // ORBITAL EVA OS</span>
      <span id="modelTag" class="brand-sub">Photorealistic PBR xEMU Digital Twin</span>
    </div>

    <div class="capsule">
      <select id="crewSelect" class="crew-select" onchange="switchCrew(this.value)">
        <option value="amira">Cdr. Amira Hassan</option>
        <option value="lukas">FE. Lukas Berg</option>
        <option value="yuki">MS. Yuki Tanaka</option>
      </select>
      <span style="color:var(--stroke)">|</span>
      <span id="clock" class="mono">MET 04:22:00</span>
    </div>
  </header>

  <div id="errBanner" class="err-banner">
    <span>&#9888;</span>
    <span id="errText"></span>
    <button onclick="openReport(document.getElementById('errBanner').dataset.aid)">View report</button>
  </div>

  <aside class="hud-wing left">
    <div id="node-neut" class="hud-node">
      <div class="node-kicker"><span>CANS Neutron</span><span>RBE 15x</span></div>
      <div id="valNeut" class="node-value">6.2 µSv/h</div>
      <div id="valCum" class="node-foot">Career: 184.2 / 600 mSv</div>
    </div>

    <div id="node-hr" class="hud-node">
      <div class="node-kicker"><span>Heart Rate</span><span>PPG</span></div>
      <div id="valHr" class="node-value">64 BPM</div>
      <canvas id="ppgWave" height="28" style="width:100%; margin-top:4px"></canvas>
    </div>

    <div id="node-ai" class="hud-node">
      <div class="node-kicker"><span>AI Co-pilot</span><span id="aiTag">LOADING</span></div>
      <div id="valAi" class="node-value">—</div>
      <div id="valAiFoot" class="node-foot">Loading models…</div>
      <div class="ai-bar"><div id="aiBarFill" class="ai-bar-fill"></div></div>
    </div>
  </aside>

  <aside class="hud-wing right">
    <div id="node-o2" class="hud-node">
      <div class="node-kicker"><span>Suit O2 & Pressure</span><span>PLSS</span></div>
      <div id="valO2Psi" class="node-value">98.6% · 4.30</div>
      <div id="valTemp" class="node-foot">Skin Temp: 36.6 °C</div>
    </div>

    <div id="node-health" class="hud-node">
      <div class="node-kicker"><span>Crew Health AI</span><span id="healthTag">...</span></div>
      <div id="valHealth" class="node-value">-- / 100</div>
      <div id="healthFeedback" class="node-foot">Waiting for telemetry...</div>
      <div id="healthAction" class="node-foot health-action"></div>
      <div class="ai-bar"><div id="healthBar" class="ai-bar-fill"></div></div>
      <button id="reportBtn" class="rpt-btn" style="display:none" onclick="openReport()">VIEW INCIDENT REPORT</button>
    </div>

    <div id="ringOrb" class="ring-orb">
      <div class="node-kicker" style="justify-content:center"><span>ASTRA-RING HAPTIC</span></div>
      <canvas id="ringMini" width="140" height="82"></canvas>
      <div id="ringLabel" class="node-foot" style="color:var(--mint); font-weight:600">Standby · Nominal</div>
    </div>
  </aside>

  <div class="dock-wrap">
    <div id="aiToast" class="ai-toast">
      <span id="toastBadge" class="toast-badge">NORMAL</span>
      <span id="toastMsg">All suit life-support and neutron sensors balanced.</span>
    </div>

    <div class="dock">
      <div class="dock-group">
        <span class="dock-label">Simulate</span>
        <button id="sc-Nominal" class="pill-btn nom active" onclick="setScenario('Nominal')">Normal</button>
        <button id="sc-Solar Storm" class="pill-btn" onclick="setScenario('Solar Storm')">Solar Storm</button>
        <button id="sc-Suit Leak" class="pill-btn" onclick="setScenario('Suit Leak')">Suit Leak</button>
        <button id="sc-Thermal Spike" class="pill-btn" onclick="setScenario('Thermal Spike')">Thermal Spike</button>
      </div>

      <div class="dock-divider"></div>

      <div class="dock-group">
        <span class="dock-label">Suit Fix</span>
        <button id="fix-shield_shelter" class="fix-btn" onclick="resolveWith('shield_shelter')">Deploy Shielding</button>
        <button id="fix-o2_boost" class="fix-btn" onclick="resolveWith('o2_boost')">O2 Pressure Purge</button>
        <button id="fix-cool_max" class="fix-btn" onclick="resolveWith('cool_max')">Max LCVG Cooling</button>
      </div>

      <div class="dock-divider"></div>

      <div class="dock-group">
        <button class="pill-btn" onclick="focusView('FULL')">Suit</button>
        <button class="pill-btn" onclick="focusView('HELMET')">Helmet</button>
        <button class="pill-btn" onclick="focusView('CHEST')">Chest</button>
        <button class="pill-btn" onclick="focusView('RING')">Ring</button>
      </div>
    </div>
  </div>

<div id="reportModal" class="modal" onclick="if (event.target === this) closeReport()">
    <div class="modal-card">
      <div class="modal-head"><span id="rptTitle">Incident report</span><button onclick="closeReport()">Close</button></div>
      <pre id="rptBody"></pre>
      <div class="modal-foot">
        <button onclick="copyReport()">Copy</button>
        <button onclick="downloadReport()">Download .txt</button>
      </div>
    </div>
  </div>

<script>
  window.addEventListener('error', () => {
    const t = document.getElementById('modelTag');
    if (t && typeof THREE === 'undefined') t.textContent = '3D engine could not load (no internet / CDN blocked) - HUD still running';
  });
  let currentAid = 'amira';
  let ppgData = [];
  let isAlert = false;

  async function setScenario(sc) {
    await fetch(`/api/crew/${currentAid}/scenario`, {
      method: 'PUT',
      headers: { 'Content-Type': 'application/json' },
      body: JSON.stringify({ scenario: sc })
    });
    poll();
  }

  async function resolveWith(key) {
    const btn = document.getElementById(`fix-${key}`);
    if (!btn.classList.contains('ready')) return;
    await fetch(`/api/crew/${currentAid}/overrides`, {
      method: 'PUT',
      headers: { 'Content-Type': 'application/json' },
      body: JSON.stringify({ [key]: true })
    });
    poll();
  }

  function updateAI(ai) {
    const node = document.getElementById('node-ai');
    const tag = document.getElementById('aiTag');
    const val = document.getElementById('valAi');
    const foot = document.getElementById('valAiFoot');
    const bar = document.getElementById('aiBarFill');
    node.classList.remove('ai-warn', 'ai-watch');
    bar.style.width = '0%';
    bar.style.background = 'var(--mint)';
    if (!ai || ai.status === 'loading') {
      tag.textContent = 'LOADING'; val.textContent = '—'; foot.textContent = 'Loading models…'; return;
    }
    if (ai.status === 'warming_up') {
      tag.textContent = 'WARM-UP'; val.textContent = '—';
      foot.textContent = `Collecting data ${ai.have || 0}/${ai.need || 10} s`; return;
    }
    if (ai.status !== 'ok') {
      tag.textContent = 'OFFLINE'; val.textContent = 'AI offline';
      foot.textContent = ai.reason || 'AI unavailable'; return;
    }
    tag.textContent = 'LIVE';
    val.textContent = `${ai.state} ${Math.round(ai.confidence * 100)}%`;
    const pct = Math.round(ai.risk * 100);
    foot.textContent = `Alert risk, next ${ai.horizon_s} s: ${pct}%` + (ai.anomaly ? ' · anomaly' : '');
    bar.style.width = pct + '%';
    if (ai.level === 'warn') { node.classList.add('ai-warn'); bar.style.background = 'var(--coral)'; }
    else if (ai.level === 'watch') { node.classList.add('ai-watch'); bar.style.background = 'var(--amber)'; }
  }

  const CREW_NAMES = {};
  let reportFor = null;
  let reportText = '';

  function updateHealth(ai) {
    const node = document.getElementById('node-health');
    const tag = document.getElementById('healthTag');
    const val = document.getElementById('valHealth');
    const fb = document.getElementById('healthFeedback');
    const act = document.getElementById('healthAction');
    const bar = document.getElementById('healthBar');
    const btn = document.getElementById('reportBtn');
    node.classList.remove('health-watch', 'health-warn', 'health-crit');
    const h = ai && ai.health;
    if (!h) {
      tag.textContent = (ai && (ai.status === 'unavailable' || ai.status === 'error')) ? 'OFFLINE' : '...';
      val.textContent = '--';
      fb.textContent = (ai && ai.reason) ? ai.reason : 'Waiting for telemetry...';
      act.textContent = '';
      bar.style.width = '0%';
      btn.style.display = 'none';
      return;
    }
    const names = { ok: 'HEALTHY', watch: 'WATCH', warning: 'WARNING', critical: 'CRITICAL' };
    const cols = { ok: 'var(--mint)', watch: 'var(--amber)', warning: 'var(--amber)', critical: 'var(--coral)' };
    tag.textContent = names[h.severity] || h.severity;
    val.textContent = `${h.score} / 100`;
    fb.textContent = h.headline;
    act.textContent = h.severity === 'ok' ? '' : ('Next: ' + ((h.actions && h.actions[0]) || 'check crew status'));
    node.title = (h.feedback || []).join(' | ');
    bar.style.width = h.score + '%';
    bar.style.background = cols[h.seve