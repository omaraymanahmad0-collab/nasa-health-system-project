
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
    bar.style.background = cols[h.sev
