'use strict';

// ── Constants ────────────────────────────────────────────────────────────────
const PIECES = {
  wK:'♔', wQ:'♕', wR:'♖', wB:'♗', wN:'♘', wP:'♙',
  bK:'♚', bQ:'♛', bR:'♜', bB:'♝', bN:'♞', bP:'♟',
};

const INIT_FEN = 'rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1';

// ── Game State ───────────────────────────────────────────────────────────────
let board       = [];   // 8×8, null or {color:'w'|'b', type:'K'|'Q'|'R'|'B'|'N'|'P'}
let turn        = 'w';
let castling    = { wK:true, wQ:true, bK:true, bQ:true };
let enPassant   = null; // {r,c} target square
let halfMove    = 0;
let fullMove    = 1;
let selected    = null; // {r,c}
let legalMoves  = [];   // [{r,c,flag}]
let history     = [];   // array of snapshots for undo
let moveLog     = [];   // SAN strings
let flipped     = false;
let gameOver    = false;

// ── FEN Parser ───────────────────────────────────────────────────────────────
function parseFen(fen) {
  const parts = fen.split(' ');
  const rows = parts[0].split('/');
  board = [];
  for (let r = 0; r < 8; r++) {
    board[r] = [];
    let c = 0;
    for (const ch of rows[r]) {
      if (/\d/.test(ch)) { for (let i = 0; i < +ch; i++) board[r][c++] = null; }
      else {
        const color = ch === ch.toUpperCase() ? 'w' : 'b';
        board[r][c++] = { color, type: ch.toUpperCase() };
      }
    }
  }
  turn = parts[1];
  const cas = parts[2];
  castling = { wK: cas.includes('K'), wQ: cas.includes('Q'), bK: cas.includes('k'), bQ: cas.includes('q') };
  if (parts[3] !== '-') {
    const fc = parts[3].charCodeAt(0) - 97;
    const fr = 8 - parseInt(parts[3][1]);
    enPassant = { r: fr, c: fc };
  } else enPassant = null;
  halfMove = parseInt(parts[4]) || 0;
  fullMove = parseInt(parts[5]) || 1;
}

// ── Board helpers ────────────────────────────────────────────────────────────
const inBounds = (r, c) => r >= 0 && r < 8 && c >= 0 && c < 8;
const opp = color => color === 'w' ? 'b' : 'w';
const cloneBoard = b => b.map(row => row.map(sq => sq ? { ...sq } : null));

function snapshot() {
  return {
    board: cloneBoard(board),
    turn, castling: { ...castling },
    enPassant: enPassant ? { ...enPassant } : null,
    halfMove, fullMove,
    moveLog: [...moveLog],
  };
}
function restore(snap) {
  board = cloneBoard(snap.board);
  turn = snap.turn;
  castling = { ...snap.castling };
  enPassant = snap.enPassant ? { ...snap.enPassant } : null;
  halfMove = snap.halfMove;
  fullMove = snap.fullMove;
  moveLog = [...snap.moveLog];
}

// ── Attack detection ─────────────────────────────────────────────────────────
function isAttacked(r, c, byColor, brd) {
  const b = brd || board;
  // Pawns
  const pd = byColor === 'w' ? 1 : -1; // direction pawns attack FROM
  for (const dc of [-1, 1]) {
    const pr = r + pd, pc = c + dc;
    if (inBounds(pr, pc) && b[pr][pc]?.color === byColor && b[pr][pc].type === 'P') return true;
  }
  // Knights
  for (const [dr, dc] of [[-2,-1],[-2,1],[-1,-2],[-1,2],[1,-2],[1,2],[2,-1],[2,1]]) {
    const nr = r+dr, nc = c+dc;
    if (inBounds(nr,nc) && b[nr][nc]?.color === byColor && b[nr][nc].type === 'N') return true;
  }
  // King
  for (const [dr, dc] of [[-1,-1],[-1,0],[-1,1],[0,-1],[0,1],[1,-1],[1,0],[1,1]]) {
    const nr = r+dr, nc = c+dc;
    if (inBounds(nr,nc) && b[nr][nc]?.color === byColor && b[nr][nc].type === 'K') return true;
  }
  // Rook / Queen (straight)
  for (const [dr, dc] of [[-1,0],[1,0],[0,-1],[0,1]]) {
    let nr = r+dr, nc = c+dc;
    while (inBounds(nr,nc)) {
      if (b[nr][nc]) {
        if (b[nr][nc].color === byColor && (b[nr][nc].type === 'R' || b[nr][nc].type === 'Q')) return true;
        break;
      }
      nr += dr; nc += dc;
    }
  }
  // Bishop / Queen (diagonal)
  for (const [dr, dc] of [[-1,-1],[-1,1],[1,-1],[1,1]]) {
    let nr = r+dr, nc = c+dc;
    while (inBounds(nr,nc)) {
      if (b[nr][nc]) {
        if (b[nr][nc].color === byColor && (b[nr][nc].type === 'B' || b[nr][nc].type === 'Q')) return true;
        break;
      }
      nr += dr; nc += dc;
    }
  }
  return false;
}

function kingPos(color, brd) {
  const b = brd || board;
  for (let r = 0; r < 8; r++)
    for (let c = 0; c < 8; c++)
      if (b[r][c]?.color === color && b[r][c].type === 'K') return { r, c };
  return null;
}

function inCheck(color, brd) {
  const kp = kingPos(color, brd);
  return kp ? isAttacked(kp.r, kp.c, opp(color), brd) : false;
}

// ── Pseudo-legal move generation ─────────────────────────────────────────────
function pseudoMoves(r, c, brd, ep, cas) {
  const b = brd || board;
  const ep2 = ep !== undefined ? ep : enPassant;
  const cas2 = cas || castling;
  const piece = b[r][c];
  if (!piece) return [];
  const { color, type } = piece;
  const moves = [];

  const add = (tr, tc, flag) => { if (inBounds(tr,tc)) moves.push({ r:tr, c:tc, flag }); };

  if (type === 'P') {
    const dir = color === 'w' ? -1 : 1;
    const startRow = color === 'w' ? 6 : 1;
    // Forward
    if (inBounds(r+dir,c) && !b[r+dir][c]) {
      add(r+dir, c, 'normal');
      if (r === startRow && !b[r+2*dir][c]) add(r+2*dir, c, 'pawn2');
    }
    // Captures
    for (const dc of [-1, 1]) {
      if (inBounds(r+dir, c+dc)) {
        if (b[r+dir][c+dc]?.color === opp(color)) add(r+dir, c+dc, 'capture');
        if (ep2 && r+dir === ep2.r && c+dc === ep2.c) add(r+dir, c+dc, 'enpassant');
      }
    }
  }

  if (type === 'N') {
    for (const [dr,dc] of [[-2,-1],[-2,1],[-1,-2],[-1,2],[1,-2],[1,2],[2,-1],[2,1]]) {
      const tr=r+dr, tc=c+dc;
      if (inBounds(tr,tc) && b[tr][tc]?.color !== color) add(tr, tc, b[tr][tc] ? 'capture' : 'normal');
    }
  }

  const slides = (dirs) => {
    for (const [dr,dc] of dirs) {
      let tr=r+dr, tc=c+dc;
      while (inBounds(tr,tc)) {
        if (b[tr][tc]) { if (b[tr][tc].color !== color) add(tr,tc,'capture'); break; }
        add(tr,tc,'normal');
        tr+=dr; tc+=dc;
      }
    }
  };

  if (type === 'B') slides([[-1,-1],[-1,1],[1,-1],[1,1]]);
  if (type === 'R') slides([[-1,0],[1,0],[0,-1],[0,1]]);
  if (type === 'Q') slides([[-1,-1],[-1,1],[1,-1],[1,1],[-1,0],[1,0],[0,-1],[0,1]]);

  if (type === 'K') {
    for (const [dr,dc] of [[-1,-1],[-1,0],[-1,1],[0,-1],[0,1],[1,-1],[1,0],[1,1]]) {
      const tr=r+dr, tc=c+dc;
      if (inBounds(tr,tc) && b[tr][tc]?.color !== color) add(tr,tc, b[tr][tc] ? 'capture' : 'normal');
    }
    // Castling
    const backRank = color === 'w' ? 7 : 0;
    if (r === backRank && c === 4) {
      // Kingside
      if (cas2[color+'K'] && !b[backRank][5] && !b[backRank][6]
          && !isAttacked(backRank,4,opp(color),b)
          && !isAttacked(backRank,5,opp(color),b)
          && !isAttacked(backRank,6,opp(color),b))
        add(backRank, 6, 'castleK');
      // Queenside
      if (cas2[color+'Q'] && !b[backRank][3] && !b[backRank][2] && !b[backRank][1]
          && !isAttacked(backRank,4,opp(color),b)
          && !isAttacked(backRank,3,opp(color),b)
          && !isAttacked(backRank,2,opp(color),b))
        add(backRank, 2, 'castleQ');
    }
  }

  return moves;
}

// ── Legal move generation (filters out moves leaving king in check) ──────────
function legalMovesFor(r, c) {
  const piece = board[r][c];
  if (!piece || piece.color !== turn) return [];
  const pseudo = pseudoMoves(r, c, board, enPassant, castling);
  return pseudo.filter(mv => {
    const b2 = cloneBoard(board);
    applyMoveToBoard(b2, r, c, mv);
    return !inCheck(piece.color, b2);
  });
}

function applyMoveToBoard(b, fr, fc, mv) {
  const piece = b[fr][fc];
  b[mv.r][mv.c] = piece;
  b[fr][fc] = null;
  if (mv.flag === 'enpassant') {
    const capRow = fr; // captured pawn stays on same rank as moving pawn's origin
    b[capRow][mv.c] = null;
  }
  if (mv.flag === 'castleK') { b[fr][5] = b[fr][7]; b[fr][7] = null; }
  if (mv.flag === 'castleQ') { b[fr][3] = b[fr][0]; b[fr][0] = null; }
}

// ── SAN generation (simplified) ──────────────────────────────────────────────
function toSAN(fr, fc, mv, promoType) {
  const piece = board[fr][fc];
  const files = 'abcdefgh';
  const dest = files[mv.c] + (8 - mv.r);
  const isCapture = mv.flag === 'capture' || mv.flag === 'enpassant';

  let san = '';
  if (mv.flag === 'castleK') return 'O-O';
  if (mv.flag === 'castleQ') return 'O-O-O';

  if (piece.type === 'P') {
    san = isCapture ? files[fc] + 'x' + dest : dest;
    if (promoType) san += '=' + promoType;
  } else {
    san = piece.type + (isCapture ? 'x' : '') + dest;
  }
  return san;
}

// ── Execute a move ────────────────────────────────────────────────────────────
function executeMove(fr, fc, mv, promoType) {
  const san = toSAN(fr, fc, mv, promoType);
  history.push(snapshot());

  const piece = board[fr][fc];
  applyMoveToBoard(board, fr, fc, mv);

  // Promotion
  if (piece.type === 'P' && (mv.r === 0 || mv.r === 7)) {
    board[mv.r][mv.c] = { color: piece.color, type: promoType || 'Q' };
  }

  // Update en passant
  enPassant = mv.flag === 'pawn2' ? { r: (fr + mv.r) / 2, c: fc } : null;

  // Update castling rights
  if (piece.type === 'K') { castling[piece.color+'K'] = false; castling[piece.color+'Q'] = false; }
  if (piece.type === 'R') {
    if (fc === 0) castling[piece.color+'Q'] = false;
    if (fc === 7) castling[piece.color+'K'] = false;
  }

  halfMove = (piece.type === 'P' || mv.flag === 'capture') ? 0 : halfMove + 1;
  if (turn === 'b') fullMove++;
  turn = opp(turn);

  // Append check/mate suffix after turn switch
  const b2 = board;
  const isC = inCheck(turn, b2);
  const hasMoves = anyLegalMoves(turn);
  if (!hasMoves) san += isC ? '#' : ' ½-½';
  else if (isC) san += '+';

  moveLog.push(san);
  return san;
}

function anyLegalMoves(color) {
  for (let r = 0; r < 8; r++)
    for (let c = 0; c < 8; c++)
      if (board[r][c]?.color === color && legalMovesFor(r, c).length > 0) return true;
  return false;
}

// ── Render ───────────────────────────────────────────────────────────────────
const boardEl       = document.getElementById('board');
const statusEl      = document.getElementById('status');
const historyEl     = document.getElementById('move-history');
const captWhiteEl   = document.getElementById('captured-white');
const captBlackEl   = document.getElementById('captured-black');
const labelWhiteEl  = document.getElementById('label-white');
const labelBlackEl  = document.getElementById('label-black');
const rankLabels    = document.getElementById('rank-labels');
const fileLabels    = document.getElementById('file-labels');
const promoModal    = document.getElementById('promo-modal');
const promoChoices  = document.getElementById('promo-choices');

let pendingPromo = null; // { fr, fc, mv }

function renderCoords() {
  rankLabels.innerHTML = '';
  fileLabels.innerHTML = '';
  const ranks = flipped ? ['1','2','3','4','5','6','7','8'] : ['8','7','6','5','4','3','2','1'];
  const files = flipped ? ['h','g','f','e','d','c','b','a'] : ['a','b','c','d','e','f','g','h'];
  ranks.forEach(r => { const s = document.createElement('span'); s.textContent = r; rankLabels.appendChild(s); });
  files.forEach(f => { const s = document.createElement('span'); s.textContent = f; fileLabels.appendChild(s); });
}

function renderBoard() {
  boardEl.innerHTML = '';
  renderCoords();

  const lastMv = history.length > 0 ? (() => {
    // find last move squares by diffing last snapshot vs current
    return null; // handled separately via lastFrom/lastTo
  })() : null;

  const kp = inCheck(turn) ? kingPos(turn) : null;

  for (let ri = 0; ri < 8; ri++) {
    for (let ci = 0; ci < 8; ci++) {
      const r = flipped ? 7 - ri : ri;
      const c = flipped ? 7 - ci : ci;

      const sq = document.createElement('div');
      sq.className = 'sq ' + ((r + c) % 2 === 0 ? 'light' : 'dark');
      sq.dataset.r = r;
      sq.dataset.c = c;

      // Highlights
      if (lastFrom && lastFrom.r === r && lastFrom.c === c) sq.classList.add('last-move');
      if (lastTo   && lastTo.r   === r && lastTo.c   === c) sq.classList.add('last-move');
      if (kp && kp.r === r && kp.c === c) sq.classList.add('in-check');
      if (selected && selected.r === r && selected.c === c) sq.classList.add('selected');

      const isLegal = legalMoves.find(m => m.r === r && m.c === c);
      if (isLegal) {
        sq.classList.add(board[r][c] ? 'legal-capture' : 'legal-move');
      }

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

  // Captured pieces
  renderCaptured();

  // Active player label
  labelWhiteEl.classList.toggle('active', turn === 'w');
  labelBlackEl.classList.toggle('active', turn === 'b');

  // Status
  if (!gameOver) {
    const inC = inCheck(turn);
    const hasMv = anyLegalMoves(turn);
    if (!hasMv) {
      gameOver = true;
      statusEl.textContent = inC
        ? (turn === 'w' ? 'Black wins by checkmate!' : 'White wins by checkmate!')
        : 'Draw by stalemate!';
    } else if (halfMove >= 100) {
      gameOver = true;
      statusEl.textContent = 'Draw by 50-move rule!';
    } else {
      statusEl.textContent = (turn === 'w' ? 'White' : 'Black') + ' to move' + (inC ? ' (Check!)' : '');
    }
  }

  // Move history
  historyEl.innerHTML = '';
  moveLog.forEach((san, i) => {
    if (i % 2 === 0) {
      const num = document.createElement('span');
      num.className = 'move-token';
      num.textContent = (Math.floor(i/2)+1) + '.';
      historyEl.appendChild(num);
    }
    const tok = document.createElement('span');
    tok.className = 'move-token ' + (i % 2 === 0 ? 'white-move' : 'black-move');
    tok.textContent = san;
    historyEl.appendChild(tok);
  });
  historyEl.scrollTop = historyEl.scrollHeight;
}

let lastFrom = null, lastTo = null;

function renderCaptured() {
  const captured = { w: [], b: [] };
  // Count pieces on board vs starting counts
  const start = { P:8, N:2, B:2, R:2, Q:1, K:1 };
  const counts = { w:{}, b:{} };
  for (const t of 'PNBRQK') { counts.w[t]=0; counts.b[t]=0; }
  for (let r=0;r<8;r++) for (let c=0;c<8;c++) if (board[r][c]) counts[board[r][c].color][board[r][c].type]++;
  for (const t of 'PNBRQK') {
    for (let i=0;i<start[t]-counts.w[t];i++) captured.b.push(PIECES['w'+t]);
    for (let i=0;i<start[t]-counts.b[t];i++) captured.w.push(PIECES['b'+t]);
  }
  captWhiteEl.textContent = captured.w.join('');
  captBlackEl.textContent = captured.b.join('');
}

// ── Interaction ───────────────────────────────────────────────────────────────
function onSquareClick(r, c) {
  if (gameOver) return;

  if (selected) {
    const mv = legalMoves.find(m => m.r === r && m.c === c);
    if (mv) {
      // Check for promotion
      const piece = board[selected.r][selected.c];
      if (piece.type === 'P' && (r === 0 || r === 7)) {
        pendingPromo = { fr: selected.r, fc: selected.c, mv };
        showPromoModal(piece.color);
        selected = null; legalMoves = [];
        return;
      }
      lastFrom = { r: selected.r, c: selected.c };
      lastTo = { r: mv.r, c: mv.c };
      executeMove(selected.r, selected.c, mv);
      selected = null; legalMoves = [];
      renderBoard();
      return;
    }
    // Clicked same piece again = deselect; other own piece = reselect
    selected = null; legalMoves = [];
  }

  const piece = board[r][c];
  if (piece && piece.color === turn) {
    selected = { r, c };
    legalMoves = legalMovesFor(r, c);
  }
  renderBoard();
}

function showPromoModal(color) {
  promoChoices.innerHTML = '';
  for (const type of ['Q','R','B','N']) {
    const btn = document.createElement('button');
    btn.className = 'promo-btn';
    btn.textContent = PIECES[color + type];
    btn.addEventListener('click', () => {
      promoModal.classList.add('hidden');
      const { fr, fc, mv } = pendingPromo;
      lastFrom = { r: fr, c: fc };
      lastTo = { r: mv.r, c: mv.c };
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
  lastFrom = null; lastTo = null;
  selected = null; legalMoves = [];
  gameOver = false;
  renderBoard();
});

function newGame() {
  parseFen(INIT_FEN);
  history = []; moveLog = [];
  selected = null; legalMoves = [];
  lastFrom = null; lastTo = null;
  gameOver = false;
  renderBoard();
}

// ── Init ──────────────────────────────────────────────────────────────────────
newGame();
