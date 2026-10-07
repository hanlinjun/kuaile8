const TOTAL_BALLS = 80;
const BALL_GRADIENTS = 5;

const ballCountInput = document.getElementById('ballCount');
const groupCountInput = document.getElementById('groupCount');
const drawBtn = document.getElementById('drawBtn');
const drumBalls = document.getElementById('drumBalls');
const displayBalls = document.getElementById('displayBalls');
const resultsList = document.getElementById('resultsList');
const progressBar = document.getElementById('progressBar');
const progressFill = document.getElementById('progressFill');
const statusText = document.getElementById('statusText');
const toggleBtns = document.querySelectorAll('.toggle-btn');

let sortEnabled = false;
let isDrawing = false;

function init() {
  renderDrumBalls();
  bindEvents();
  showEmptyResults();
}

function bindEvents() {
  document.querySelectorAll('.btn-adjust').forEach(btn => {
    btn.addEventListener('click', () => {
      const input = document.getElementById(btn.dataset.target);
      const min = parseInt(input.min, 10);
      const max = parseInt(input.max, 10);
      let val = parseInt(input.value, 10) + parseInt(btn.dataset.delta, 10);
      val = Math.max(min, Math.min(max, val));
      input.value = val;
    });
  });

  ballCountInput.addEventListener('change', () => clampInput(ballCountInput, 1, 80));
  groupCountInput.addEventListener('change', () => clampInput(groupCountInput, 1, 20));

  toggleBtns.forEach(btn => {
    btn.addEventListener('click', () => {
      toggleBtns.forEach(b => b.classList.remove('active'));
      btn.classList.add('active');
      sortEnabled = btn.dataset.sort === 'true';
    });
  });

  drawBtn.addEventListener('click', startDraw);
}

function clampInput(input, min, max) {
  let val = parseInt(input.value, 10);
  if (isNaN(val)) val = min;
  input.value = Math.max(min, Math.min(max, val));
}

function renderDrumBalls() {
  drumBalls.innerHTML = '';
  const sample = shuffle(Array.from({ length: TOTAL_BALLS }, (_, i) => i + 1)).slice(0, 24);
  sample.forEach(num => {
    const el = document.createElement('div');
    el.className = 'drum-ball';
    el.textContent = num;
    drumBalls.appendChild(el);
  });
}

function shuffle(arr) {
  const a = [...arr];
  for (let i = a.length - 1; i > 0; i--) {
    const j = Math.floor(Math.random() * (i + 1));
    [a[i], a[j]] = [a[j], a[i]];
  }
  return a;
}

function drawGroup(ballCount) {
  return shuffle(Array.from({ length: TOTAL_BALLS }, (_, i) => i + 1)).slice(0, ballCount);
}

function showEmptyResults() {
  resultsList.innerHTML = '<div class="empty-results">摇奖结果将显示在这里</div>';
}

function setControlsEnabled(enabled) {
  drawBtn.disabled = !enabled;
  ballCountInput.disabled = !enabled;
  groupCountInput.disabled = !enabled;
  document.querySelectorAll('.btn-adjust, .toggle-btn').forEach(el => {
    el.disabled = !enabled;
  });
}

async function startDraw() {
  if (isDrawing) return;

  const ballCount = parseInt(ballCountInput.value, 10);
  const groupCount = parseInt(groupCountInput.value, 10);

  if (ballCount < 1 || ballCount > 80 || groupCount < 1 || groupCount > 20) return;

  isDrawing = true;
  setControlsEnabled(false);
  drawBtn.classList.add('drawing');
  drawBtn.querySelector('.btn-text').textContent = '摇奖中...';
  resultsList.innerHTML = '';
  progressBar.classList.add('visible');
  progressFill.style.width = '0%';

  const allResults = [];

  for (let g = 0; g < groupCount; g++) {
    const progress = ((g + 0.5) / groupCount) * 100;
    progressFill.style.width = `${progress}%`;
    statusText.textContent = `正在摇第 ${g + 1} / ${groupCount} 组...`;

    const numbers = drawGroup(ballCount);
    const display = sortEnabled ? [...numbers].sort((a, b) => a - b) : numbers;

    await animateGroupDraw(display, g + 1, groupCount);
    allResults.push({ group: g + 1, numbers: display, sorted: sortEnabled });

    appendResultGroup(allResults[g], g);
    progressFill.style.width = `${((g + 1) / groupCount) * 100}%`;

    if (g < groupCount - 1) {
      await sleep(400);
    }
  }

  statusText.textContent = `摇奖完成！共 ${groupCount} 组，每组 ${ballCount} 个球`;
  drumBalls.classList.remove('shaking');
  isDrawing = false;
  setControlsEnabled(true);
  drawBtn.classList.remove('drawing');
  drawBtn.querySelector('.btn-text').textContent = '开始摇奖';
}

async function animateGroupDraw(numbers, groupIndex, totalGroups) {
  displayBalls.innerHTML = '';
  drumBalls.classList.add('shaking');

  const drumInterval = setInterval(() => {
    drumBalls.querySelectorAll('.drum-ball').forEach(el => {
      el.textContent = Math.floor(Math.random() * TOTAL_BALLS) + 1;
    });
  }, 80);

  await sleep(600 + Math.random() * 300);

  for (let i = 0; i < numbers.length; i++) {
    statusText.textContent = `第 ${groupIndex}/${totalGroups} 组 · 摇出第 ${i + 1} 个球...`;

    const rolling = document.createElement('div');
    rolling.className = 'rolling-ball';
    rolling.textContent = '?';
    displayBalls.appendChild(rolling);

    let rollCount = 0;
    const maxRolls = 12 + Math.floor(Math.random() * 8);

    await new Promise(resolve => {
      const rollInterval = setInterval(() => {
        rolling.textContent = Math.floor(Math.random() * TOTAL_BALLS) + 1;
        rollCount++;
        if (rollCount >= maxRolls) {
          clearInterval(rollInterval);
          resolve();
        }
      }, 60);
    });

    rolling.remove();

    const ball = document.createElement('div');
    ball.className = 'result-ball';
    ball.textContent = numbers[i];
    ball.style.animationDelay = '0s';
    displayBalls.appendChild(ball);

    requestAnimationFrame(() => ball.classList.add('revealed'));

    await sleep(350);
  }

  clearInterval(drumInterval);
  renderDrumBalls();
}

function appendResultGroup(result, index) {
  const group = document.createElement('div');
  group.className = 'result-group';
  group.style.animationDelay = `${index * 0.1}s`;

  const sortLabel = result.sorted ? '已排序' : '原始顺序';

  group.innerHTML = `
    <div class="result-group-header">
      <span class="result-group-title">第 ${result.group} 组</span>
      <span class="result-group-meta">${sortLabel} · ${result.numbers.length} 个球</span>
    </div>
    <div class="result-group-balls">
      ${result.numbers.map(n => `<div class="mini-ball">${n}</div>`).join('')}
    </div>
  `;

  resultsList.appendChild(group);
}

function sleep(ms) {
  return new Promise(resolve => setTimeout(resolve, ms));
}

init();
