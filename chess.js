'use strict';

// ── Constants ────────────────────────────────────────────────────────────────
const PIECES = {
  wK:'♔', wQ:'♕', wR:'♖', wB:'♗', wN:'♘', wP:'♙',
  bK:'♚', bQ:'♛', bR:'♜', bB:'♝', bN:'♞', bP:'♟',
};

const INIT_FEN = 'rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1';

// ── Game State ───────────────────────────────────────────────────────────────
let board      = [];
let turn       = 'w';
let castling   = { wK:true, wQ:true, bK:true, bQ:true };
let enPassant  = null;   // {r,c} target square or null
let halfMove   = 0;
let fullMove   = 1;
let selected   = null;   // {r,c} or null
let legalMoves = [];
let history    = [];     // snapshots for undo
let moveLog    = [];     // SAN strings
let flipped    = false;
let gameOver   = false;
let lastFrom   = null;
let lastTo     = null;
let pendingPromo = null; // { fr, fc, mv }

// ── FEN Parser ───────────────────────────────────────────────────────────────
function parseFen(fen) {
  const parts = fen.split(' ');
  const rows  = parts[0].split('/');
  board = [];
  for (let r = 0; r < 8; r++) {
    board[r] = [];
    let c = 0;
    for (const ch of rows[r]) {
      if (/\d/.test(ch)) {
        for (let i = 0; i < +ch; i++) board[r][c++] = null;
      } else {
        const color = ch === ch.toUpperCase() ? 'w' : 'b';
        board[r][c++] = { color, type: ch.toUpperCase() };
      }
    }
  }
  turn = parts[1];
  const cas = parts[2];
  castling = {
    wK: cas.includes('K'), wQ: cas.includes('Q'),
    bK: cas.includes('k'), bQ: cas.includes('q'),
  };
  if (parts[3] !== '-') {
    const fc = parts[3].charCodeAt(0) - 97;
    const fr = 8 - parseInt(parts[3][1]);
    enPassant = { r: fr, c: fc };
  } else {
    enPassant = null;
  }
  halfMove = parseInt(parts[4]) || 0;
  fullMove = parseInt(parts[5]) || 1;
}

// ── Board helpers ────────────────────────────────────────────────────────────
const inBounds  = (r, c) => r >= 0 && r < 8 && c >= 0 && c < 8;
const opp       = color  => color === 'w' ? 'b' : 'w';
const cloneBoard = b     => b.map(row => row.map(sq => sq ? { ...sq } : null));

function snapshot() {
  return {
    board: cloneBoard(board),
    turn,
    castling:   { ...castling },
    enPassant:  enPassant ? { ...enPassant } : null,
    halfMove,
    fullMove,
    moveLog:    [...moveLog],
    lastFrom:   lastFrom ? { ...lastFrom } : null,
    lastTo:     lastTo   ? { ...lastTo }   : null,
  };
}

function restore(snap) {
  board     = cloneBoard(snap.board);
  turn      = snap.turn;
  castling  = { ...snap.castling };
  enPassant = snap.enPassant ? { ...snap.enPassant } : null;
  halfMove  = snap.halfMove;
  fullMove  = snap.fullMove;
  moveLog   = [...snap.moveLog];
  lastFrom  = snap.lastFrom ? { ...snap.lastFrom } : null;
  lastTo    = snap.lastTo   ? { ...snap.lastTo }   : null;
}

// ── Attack detection ─────────────────────────────────────────────────────────
function isAttacked(r, c, byColor, b) {
  // Pawns — white pawns sit one rank below (higher row index) what they attack
  const pd = byColor === 'w' ? 1 : -1;
  for (const dc of [-1, 1]) {
    const pr = r + pd, pc = c + dc;
    if (inBounds(pr, pc) && b[pr][pc]?.color === byColor && b[pr][pc].type === 'P') return true;
  }
  // Knights
  for (const [dr, dc] of [[-2,-1],[-2,1],[-1,-2],[-1,2],[1,-2],[1,2],[2,-1],[2,1]]) {
    const nr = r + dr, nc = c + dc;
    if (inBounds(nr, nc) && b[nr][nc]?.color === byColor && b[nr][nc].type === 'N') return true;
  }
  // King
  for (const [dr, dc] of [[-1,-1],[-1,0],[-1,1],[0,-1],[0,1],[1,-1],[1,0],[1,1]]) {
    const nr = r + dr, nc = c + dc;
    if (inBounds(nr, nc) && b[nr][nc]?.color === byColor && b[nr][nc].type === 'K') return true;
  }
  // Rook / Queen (orthogonal)
  for (const [dr, dc] of [[-1,0],[1,0],[0,-1],[0,1]]) {
    let nr = r + dr, nc = c + dc;
    while (inBounds(nr, nc)) {
      if (b[nr][nc]) {
        if (b[nr][nc].color === byColor && (b[nr][nc].type === 'R' || b[nr][nc].type === 'Q')) return true;
        break;
      }
      nr += dr; nc += dc;
    }
  }
  // Bishop / Queen (diagonal)
  for (const [dr, dc] of [[-1,-1],[-1,1],[1,-1],[1,1]]) {
    let nr = r + dr, nc = c + dc;
    while (inBounds(nr, nc)) {
      if (b[nr][nc]) {
        if (b[nr][nc].color === byColor && (b[nr][nc].type === 'B' || b[nr][nc].type === 'Q')) return true;
        break;
      }
      nr += dr; nc += dc;
    }
  }
  return false;
}

function kingPos(color, b) {
  for (let r = 0; r < 8; r++)
    for (let c = 0; c < 8; c++)
      if (b[r][c]?.color === color && b[r][c].type === 'K') return { r, c };
  return null;
}

function inCheck(color, b) {
  const kp = kingPos(color, b);
  return kp ? isAttacked(kp.r, kp.c, opp(color), b) : false;
}

// ── Pseudo-legal move generation ─────────────────────────────────────────────
function pseudoMoves(r, c, b, ep, cas) {
  const piece = b[r][c];
  if (!piece) return [];
  const { color, type } = piece;
  const moves = [];

  const add = (tr, tc, flag) => { if (inBounds(tr, tc)) moves.push({ r: tr, c: tc, flag }); };

  if (type === 'P') {
    const dir      = color === 'w' ? -1 : 1;
    const startRow = color === 'w' ?  6 : 1;
    // Forward push
    if (inBounds(r + dir, c) && !b[r + dir][c]) {
      add(r + dir, c, 'normal');
      if (r === startRow && !b[r + 2 * dir][c]) add(r + 2 * dir, c, 'pawn2');
    }
    // Diagonal captures + en passant
    for (const dc of [-1, 1]) {
      if (!inBounds(r + dir, c + dc)) continue;
      if (b[r + dir][c + dc]?.color === opp(color)) add(r + dir, c + dc, 'capture');
      if (ep && r + dir === ep.r && c + dc === ep.c)  add(r + dir, c + dc, 'enpassant');
    }
  }

  if (type === 'N') {
    for (const [dr, dc] of [[-2,-1],[-2,1],[-1,-2],[-1,2],[1,-2],[1,2],[2,-1],[2,1]]) {
      const tr = r + dr, tc = c + dc;
      if (inBounds(tr, tc) && b[tr][tc]?.color !== color)
        add(tr, tc, b[tr][tc] ? 'capture' : 'normal');
    }
  }

  const slide = (dirs) => {
    for (const [dr, dc] of dirs) {
      let tr = r + dr, tc = c + dc;
      while (inBounds(tr, tc)) {
        if (b[tr][tc]) { if (b[tr][tc].color !== color) add(tr, tc, 'capture'); break; }
        add(tr, tc, 'normal');
        tr += dr; tc += dc;
      }
    }
  };
  if (type === 'B') slide([[-1,-1],[-1,1],[1,-1],[1,1]]);
  if (type === 'R') slide([[-1,0],[1,0],[0,-1],[0,1]]);
  if (type === 'Q') slide([[-1,-1],[-1,1],[1,-1],[1,1],[-1,0],[1,0],[0,-1],[0,1]]);

  if (type === 'K') {
    for (const [dr, dc] of [[-1,-1],[-1,0],[-1,1],[0,-1],[0,1],[1,-1],[1,0],[1,1]]) {
      const tr = r + dr, tc = c + dc;
      if (inBounds(tr, tc) && b[tr][tc]?.color !== color)
        add(tr, tc, b[tr][tc] ? 'capture' : 'normal');
    }
    // Castling — king must be on its starting square and not in check
    const back = color === 'w' ? 7 : 0;
    if (r === back && c === 4 && !isAttacked(back, 4, opp(color), b)) {
      if (cas[color + 'K'] && !b[back][5] && !b[back][6]
          && !isAttacked(back, 5, opp(color), b)
          && !isAttacked(back, 6, opp(color), b))
        add(back, 6, 'castleK');
      if (cas[color + 'Q'] && !b[back][3] && !b[back][2] && !b[back][1]
          && !isAttacked(back, 3, opp(color), b)
          && !isAttacked(back, 2, opp(color), b))
        add(back, 2, 'castleQ');
    }
  }

  return moves;
}

// ── Apply move to a board copy ────────────────────────────────────────────────
function applyMoveToBoard(b, fr, fc, mv) {
  const piece = b[fr][fc];
  b[mv.r][mv.c] = piece;
  b[fr][fc]     = null;
  if (mv.flag === 'enpassant') b[fr][mv.c] = null;   // remove captured pawn
  if (mv.flag === 'castleK')  { b[fr][5] = b[fr][7]; b[fr][7] = null; }
  if (mv.flag === 'castleQ')  { b[fr][3] = b[fr][0]; b[fr][0] = null; }
}

// ── Legal move generation ─────────────────────────────────────────────────────
function legalMovesFor(r, c) {
  const piece = board[r][c];
  if (!piece || piece.color !== turn) return [];
  return pseudoMoves(r, c, board, enPassant, castling).filter(mv => {
    const b2 = cloneBoard(board);
    applyMoveToBoard(b2, r, c, mv);
    return !inCheck(piece.color, b2);
  });
}

function anyLegalMoves(color) {
  for (let r = 0; r < 8; r++)
    for (let c = 0; c < 8; c++)
      if (board[r][c]?.color === color && legalMovesFor(r, c).length > 0) return true;
  return false;
}

// ── SAN generation ────────────────────────────────────────────────────────────
function toSAN(fr, fc, mv, promoType) {
  const piece = board[fr][fc];
  const files  = 'abcdefgh';
  const dest   = files[mv.c] + (8 - mv.r);
  const isCapt = mv.flag === 'capture' || mv.flag === 'enpassant';

  if (mv.flag === 'castleK') return 'O-O';
  if (mv.flag === 'castleQ') return 'O-O-O';

  if (piece.type === 'P') {
    let s = isCapt ? files[fc] + 'x' + dest : dest;
    if (promoType) s += '=' + promoType;
    return s;
  }
  // Sliding / jumping piece — minimal disambiguation (no ambiguity detection needed for display)
  return piece.type + (isCapt ? 'x' : '') + dest;
}

// ── Execute a move ────────────────────────────────────────────────────────────
function executeMove(fr, fc, mv, promoType) {
  let san = toSAN(fr, fc, mv, promoType);  // let, not const — we append +/# later
  history.push(snapshot());

  const piece = board[fr][fc];
  applyMoveToBoard(board, fr, fc, mv);

  // Promotion
  if (piece.type === 'P' && (mv.r === 0 || mv.r === 7)) {
    board[mv.r][mv.c] = { color: piece.color, type: promoType || 'Q' };
  }

  // En passant target for next move
  enPassant = mv.flag === 'pawn2' ? { r: (fr + mv.r) / 2, c: fc } : null;

  // Castling rights — moving king or rook
  if (piece.type === 'K') { castling[piece.color + 'K'] = false; castling[piece.color + 'Q'] = false; }
  if (piece.type === 'R') {
    const backRank = piece.color === 'w' ? 7 : 0;
    if (fr === backRank && fc === 0) castling[piece.color + 'Q'] = false;
    if (fr === backRank && fc === 7) castling[piece.color + 'K'] = false;
  }
  // If a rook is captured on its starting square, revoke that castling right
  if (mv.r === 0 && mv.c === 7) castling.bK = false;
  if (mv.r === 0 && mv.c === 0) castling.bQ = false;
  if (mv.r === 7 && mv.c === 7) castling.wK = false;
  if (mv.r === 7 && mv.c === 0) castling.wQ = false;

  halfMove = (piece.type === 'P' || mv.flag === 'capture' || mv.flag === 'enpassant') ? 0 : halfMove + 1;
  if (turn === 'b') fullMove++;
  turn = opp(turn);

  // Append check/checkmate suffix now that the board reflects the new position
  const nowInCheck  = inCheck(turn, board);
  const nowHasMoves = anyLegalMoves(turn);
  if (!nowHasMoves && nowInCheck)  san += '#';
  else if (nowInCheck)             san += '+';

  moveLog.push(san);
  lastFrom = { r: fr, c: fc };
  lastTo   = { r: mv.r, c: mv.c };
}

// ── Render ────────────────────────────────────────────────────────────────────
const boardEl      = document.getElementById('board');
const statusEl     = document.getElementById('status');
const historyEl    = document.getElementById('move-history');
const captWhiteEl  = document.getElementById('captured-white');
const captBlackEl  = document.getElementById('captured-black');
const labelWhiteEl = document.getElementById('label-white');
const labelBlackEl = document.getElementById('label-black');
const rankLabels   = document.getElementById('rank-labels');
const fileLabels   = document.getElementById('file-labels');
const promoModal   = document.getElementById('promo-modal');
const promoChoices = document.getElementById('promo-choices');

function renderCoords() {
  rankLabels.innerHTML = '';
  fileLabels.innerHTML = '';
  const ranks = flipped ? ['1','2','3','4','5','6','7','8'] : ['8','7','6','5','4','3','2','1'];
  const files  = flipped ? ['h','g','f','e','d','c','b','a'] : ['a','b','c','d','e','f','g','h'];
  ranks.forEach(r => { const s = document.createElement('span'); s.textContent = r; rankLabels.appendChild(s); });
  files.forEach(f => { const s = document.createElement('span'); s.textContent = f; fileLabels.appendChild(s); });
}

function renderBoard() {
  boardEl.innerHTML = '';
  renderCoords();

  const checkedKing = inCheck(turn, board) ? kingPos(turn, board) : null;

  for (let ri = 0; ri < 8; ri++) {
    for (let ci = 0; ci < 8; ci++) {
      const r = flipped ? 7 - ri : ri;
      const c = flipped ? 7 - ci : ci;

      const sq = document.createElement('div');
      sq.className = 'sq ' + ((r + c) % 2 === 0 ? 'light' : 'dark');

      if (lastFrom && lastFrom.r === r && lastFrom.c === c) sq.classList.add('last-move');
      if (lastTo   && lastTo.r   === r && lastTo.c   === c) sq.classList.add('last-move');
      if (checkedKing && checkedKing.r === r && checkedKing.c === c) sq.classList.add('in-check');
      if (selected && selected.r === r && selected.c === c) sq.classList.add('selected');

      const lm = legalMoves.find(m => m.r === r && m.c === c);
      if (lm) sq.classList.add(board[r][c] ? 'legal-capture' : 'legal-move');

      const piece = board[r][c];
      if (piece) {
        const pd = document.createElement('div');
        pd.className = 'piece';
        pd.textContent = PIECES[piece.color + piece.type];
        sq.appendChild(pd);
      }

      sq.addEventListener('click', () => onSquareClick(r, c));
      boardEl.appendChild(sq);
    }
  }

  renderCaptured();

  labelWhiteEl.classList.toggle('active', turn === 'w');
  labelBlackEl.classList.toggle('active', turn === 'b');

  if (!gameOver) {
    const isC   = inCheck(turn, board);
    const hasMv = anyLegalMoves(turn);
    if (!hasMv && isC) {
      gameOver = true;
      statusEl.textContent = turn === 'w' ? 'Black wins by checkmate!' : 'White wins by checkmate!';
    } else if (!hasMv) {
      gameOver = true;
      statusEl.textContent = 'Draw by stalemate!';
    } else if (halfMove >= 100) {
      gameOver = true;
      statusEl.textContent = 'Draw by 50-move rule!';
    } else {
      statusEl.textContent = (turn === 'w' ? 'White' : 'Black') + ' to move' + (isC ? ' — Check!' : '');
    }
  }

  historyEl.innerHTML = '';
  moveLog.forEach((san, i) => {
    if (i % 2 === 0) {
      const num = document.createElement('span');
      num.className = 'move-token';
      num.textContent = (Math.floor(i / 2) + 1) + '.';
      historyEl.appendChild(num);
    }
    const tok = document.createElement('span');
    tok.className = 'move-token ' + (i % 2 === 0 ? 'white-move' : 'black-move');
    tok.textContent = san;
    historyEl.appendChild(tok);
  });
  historyEl.scrollTop = historyEl.scrollHeight;
}

function renderCaptured() {
  const start  = { P:8, N:2, B:2, R:2, Q:1, K:1 };
  const counts = { w: {P:0,N:0,B:0,R:0,Q:0,K:0}, b: {P:0,N:0,B:0,R:0,Q:0,K:0} };
  for (let r = 0; r < 8; r++)
    for (let c = 0; c < 8; c++)
      if (board[r][c]) counts[board[r][c].color][board[r][c].type]++;

  let captByBlack = '', captByWhite = '';
  for (const t of 'QRBNP') {
    const wLost = Math.max(0, start[t] - counts.w[t]);
    const bLost = Math.max(0, start[t] - counts.b[t]);
    for (let i = 0; i < wLost; i++) captByBlack += PIECES['w' + t];
    for (let i = 0; i < bLost; i++) captByWhite += PIECES['b' + t];
  }
  captWhiteEl.textContent = captByWhite;
  captBlackEl.textContent = captByBlack;
}

// ── Interaction ───────────────────────────────────────────────────────────────
function onSquareClick(r, c) {
  if (gameOver) return;

  if (selected) {
    const mv = legalMoves.find(m => m.r === r && m.c === c);
    if (mv) {
      const piece = board[selected.r][selected.c];
      if (piece.type === 'P' && (r === 0 || r === 7)) {
        // Need promotion choice before executing
        pendingPromo = { fr: selected.r, fc: selected.c, mv };
        selected = null; legalMoves = [];
        showPromoModal(piece.color);
        return;
      }
      executeMove(selected.r, selected.c, mv);
      selected = null; legalMoves = [];
      renderBoard();
      return;
    }
    // Click on own piece = reselect; click elsewhere = deselect
    selected = null; legalMoves = [];
  }

  const piece = board[r][c];
  if (piece && piece.color === turn) {
    selected   = { r, c };
    legalMoves = legalMovesFor(r, c);
  }
  renderBoard();
}

function showPromoModal(color) {
  promoChoices.innerHTML = '';
  for (const type of ['Q', 'R', 'B', 'N']) {
    const btn = document.createElement('button');
    btn.className = 'promo-btn';
    btn.textContent = PIECES[color + type];
    btn.addEventListener('click', () => {
      promoModal.classList.add('hidden');
      const { fr, fc, mv } = pendingPromo;
      executeMove(fr, fc, mv, type);
      pendingPromo = null;
      renderBoard();
    });
    promoChoices.appendChild(btn);
  }
  promoModal.classList.remove('hidden');
}

// ── Controls ──────────────────────────────────────────────────────────────────
document.getElementById('btn-new').addEventListener('click', () => {
  if (!gameOver && history.length > 0 && !confirm('Start a new game?')) return;
  newGame();
});

document.getElementById('btn-flip').addEventListener('click', () => {
  flipped = !flipped;
  renderBoard();
});

document.getElementById('btn-undo').addEventListener('click', () => {
  if (history.length === 0) return;
  restore(history.pop());
  selected = null; legalMoves = [];
  gameOver = false;
  renderBoard();
});

// ── Init ──────────────────────────────────────────────────────────────────────
function newGame() {
  parseFen(INIT_FEN);
  history  = []; moveLog = [];
  selected = null; legalMoves = [];
  lastFrom = null; lastTo = null;
  gameOver = false;
  renderBoard();
}

newGame();
