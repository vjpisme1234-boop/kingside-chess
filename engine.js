// Chess rules + computer player. Runs on the page (rules) and as a Web Worker (search).
var ChessEngine = (function () {
  'use strict';

  var PAWN = 1, KNIGHT = 2, BISHOP = 3, ROOK = 4, QUEEN = 5, KING = 6;
  var WHITE = 0, BLACK = 8;
  var F_EP = 1, F_CASTLE = 2, F_DOUBLE = 4;
  var MATE = 100000, INF = 1000000;

  // Squares: a1 = 0, h1 = 7, a8 = 56. Piece = color | type.
  var KN = [], KG = [], RAYS = [], PAWN_ATT = [[], [], [], [], [], [], [], [], []];
  var DIRS = [[0, 1], [0, -1], [1, 0], [-1, 0], [1, 1], [1, -1], [-1, 1], [-1, -1]];
  (function () {
    var kn = [[1, 2], [2, 1], [2, -1], [1, -2], [-1, -2], [-2, -1], [-2, 1], [-1, 2]];
    for (var sq = 0; sq < 64; sq++) {
      var f = sq & 7, r = sq >> 3, i, nf, nr;
      KN[sq] = []; KG[sq] = []; RAYS[sq] = [];
      for (i = 0; i < 8; i++) {
        nf = f + kn[i][0]; nr = r + kn[i][1];
        if (nf >= 0 && nf < 8 && nr >= 0 && nr < 8) KN[sq].push(nr * 8 + nf);
        nf = f + DIRS[i][0]; nr = r + DIRS[i][1];
        if (nf >= 0 && nf < 8 && nr >= 0 && nr < 8) KG[sq].push(nr * 8 + nf);
        var ray = [];
        nf = f + DIRS[i][0]; nr = r + DIRS[i][1];
        while (nf >= 0 && nf < 8 && nr >= 0 && nr < 8) {
          ray.push(nr * 8 + nf); nf += DIRS[i][0]; nr += DIRS[i][1];
        }
        RAYS[sq].push(ray);
      }
      // Squares a pawn of each color standing on sq attacks.
      PAWN_ATT[WHITE][sq] = []; PAWN_ATT[BLACK][sq] = [];
      if (r < 7) { if (f > 0) PAWN_ATT[WHITE][sq].push(sq + 7); if (f < 7) PAWN_ATT[WHITE][sq].push(sq + 9); }
      if (r > 0) { if (f > 0) PAWN_ATT[BLACK][sq].push(sq - 9); if (f < 7) PAWN_ATT[BLACK][sq].push(sq - 7); }
    }
  })();

  var CASTLE_MASK = [];
  for (var s = 0; s < 64; s++) CASTLE_MASK[s] = 15;
  CASTLE_MASK[0] = ~2 & 15; CASTLE_MASK[7] = ~1 & 15; CASTLE_MASK[4] = ~3 & 15;
  CASTLE_MASK[56] = ~8 & 15; CASTLE_MASK[63] = ~4 & 15; CASTLE_MASK[60] = ~12 & 15;

  function mFrom(m) { return m & 63; }
  function mTo(m) { return (m >> 6) & 63; }
  function mPromo(m) { return (m >> 12) & 7; }
  function mFlag(m) { return (m >> 15) & 7; }
  function encode(from, to, promo, flag) { return from | (to << 6) | (promo << 12) | (flag << 15); }

  var FILES = 'abcdefgh';
  function sqName(sq) { return FILES[sq & 7] + ((sq >> 3) + 1); }
  function sqParse(s) { return (s.charCodeAt(1) - 49) * 8 + (s.charCodeAt(0) - 97); }
  var LETTERS = ' pnbrqk';

  function Position(fen) {
    this.b = new Int8Array(64);
    this.turn = WHITE; this.castle = 0; this.ep = -1; this.half = 0; this.full = 1;
    this.kings = [];
    this.stack = [];
    this.load(fen || 'rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1');
  }

  Position.prototype.load = function (fen) {
    var parts = fen.trim().split(/\s+/), rows = parts[0].split('/');
    this.b.fill(0);
    for (var r = 0; r < 8; r++) {
      var f = 0, row = rows[7 - r];
      for (var i = 0; i < row.length; i++) {
        var c = row[i];
        if (c >= '1' && c <= '8') { f += +c; continue; }
        var lower = c.toLowerCase(), color = c === lower ? BLACK : WHITE;
        var p = color | LETTERS.indexOf(lower);
        this.b[r * 8 + f] = p;
        if ((p & 7) === KING) this.kings[color] = r * 8 + f;
        f++;
      }
    }
    this.turn = parts[1] === 'b' ? BLACK : WHITE;
    var cs = parts[2] || '-';
    this.castle = (cs.indexOf('K') >= 0 ? 1 : 0) | (cs.indexOf('Q') >= 0 ? 2 : 0) |
                  (cs.indexOf('k') >= 0 ? 4 : 0) | (cs.indexOf('q') >= 0 ? 8 : 0);
    this.ep = parts[3] && parts[3] !== '-' ? sqParse(parts[3]) : -1;
    this.half = parts[4] ? +parts[4] : 0;
    this.full = parts[5] ? +parts[5] : 1;
    this.stack = [];
  };

  Position.prototype.fen = function () {
    var out = '';
    for (var r = 7; r >= 0; r--) {
      var empty = 0;
      for (var f = 0; f < 8; f++) {
        var p = this.b[r * 8 + f];
        if (!p) { empty++; continue; }
        if (empty) { out += empty; empty = 0; }
        var l = LETTERS[p & 7];
        out += p & BLACK ? l : l.toUpperCase();
      }
      if (empty) out += empty;
      if (r) out += '/';
    }
    var cs = (this.castle & 1 ? 'K' : '') + (this.castle & 2 ? 'Q' : '') + (this.castle & 4 ? 'k' : '') + (this.castle & 8 ? 'q' : '');
    return out + ' ' + (this.turn ? 'b' : 'w') + ' ' + (cs || '-') + ' ' +
      (this.ep >= 0 ? sqName(this.ep) : '-') + ' ' + this.half + ' ' + this.full;
  };

  // Key for repetition: placement, side, castling and an en-passant square only when a capture there is possible.
  Position.prototype.key = function () {
    var epPart = '-';
    if (this.ep >= 0) {
      var them = this.turn ^ BLACK, att = PAWN_ATT[them][this.ep];
      for (var i = 0; i < att.length; i++) if (this.b[att[i]] === (this.turn | PAWN)) { epPart = sqName(this.ep); break; }
    }
    return this.fen().split(' ').slice(0, 3).join(' ') + ' ' + epPart;
  };

  Position.prototype.attacked = function (sq, by) {
    var b = this.b, i, list, ray, j, p;
    list = PAWN_ATT[by ^ BLACK][sq];
    for (i = 0; i < list.length; i++) if (b[list[i]] === (by | PAWN)) return true;
    list = KN[sq];
    for (i = 0; i < list.length; i++) if (b[list[i]] === (by | KNIGHT)) return true;
    list = KG[sq];
    for (i = 0; i < list.length; i++) if (b[list[i]] === (by | KING)) return true;
    for (i = 0; i < 8; i++) {
      ray = RAYS[sq][i];
      for (j = 0; j < ray.length; j++) {
        p = b[ray[j]];
        if (!p) continue;
        if ((p & BLACK) === by) {
          var t = p & 7;
          if (t === QUEEN || (i < 4 ? t === ROOK : t === BISHOP)) return true;
        }
        break;
      }
    }
    return false;
  };

  Position.prototype.inCheck = function (color) {
    if (color === undefined) color = this.turn;
    return this.attacked(this.kings[color], color ^ BLACK);
  };

  // Pseudo-legal moves; capturesOnly adds captures and queen promotions (for quiescence search).
  Position.prototype.gen = function (capturesOnly) {
    var b = this.b, us = this.turn, them = us ^ BLACK, out = [];
    for (var sq = 0; sq < 64; sq++) {
      var p = b[sq];
      if (!p || (p & BLACK) !== us) continue;
      var t = p & 7, i, j, to, q, list;
      if (t === PAWN) {
        var dir = us ? -8 : 8, rank = sq >> 3, startRank = us ? 6 : 1, promoRank = us ? 1 : 6;
        to = sq + dir;
        if (!b[to]) {
          if (rank === promoRank) {
            out.push(encode(sq, to, QUEEN, 0));
            if (!capturesOnly) { out.push(encode(sq, to, ROOK, 0)); out.push(encode(sq, to, BISHOP, 0)); out.push(encode(sq, to, KNIGHT, 0)); }
          } else if (!capturesOnly) {
            out.push(encode(sq, to, 0, 0));
            if (rank === startRank && !b[to + dir]) out.push(encode(sq, to + dir, 0, F_DOUBLE));
          }
        }
        list = PAWN_ATT[us][sq];
        for (i = 0; i < list.length; i++) {
          to = list[i];
          q = b[to];
          if (q && (q & BLACK) === them) {
            if (rank === promoRank) {
              out.push(encode(sq, to, QUEEN, 0));
              if (!capturesOnly) { out.push(encode(sq, to, ROOK, 0)); out.push(encode(sq, to, BISHOP, 0)); out.push(encode(sq, to, KNIGHT, 0)); }
            } else out.push(encode(sq, to, 0, 0));
          } else if (to === this.ep) out.push(encode(sq, to, 0, F_EP));
        }
      } else if (t === KNIGHT || t === KING) {
        list = t === KNIGHT ? KN[sq] : KG[sq];
        for (i = 0; i < list.length; i++) {
          to = list[i]; q = b[to];
          if (q ? (q & BLACK) === them : !capturesOnly) out.push(encode(sq, to, 0, 0));
        }
        if (t === KING && !capturesOnly) this.genCastles(sq, out);
      } else {
        var d0 = t === BISHOP ? 4 : 0, d1 = t === ROOK ? 4 : 8;
        for (i = d0; i < d1; i++) {
          var ray = RAYS[sq][i];
          for (j = 0; j < ray.length; j++) {
            to = ray[j]; q = b[to];
            if (!q) { if (!capturesOnly) out.push(encode(sq, to, 0, 0)); continue; }
            if ((q & BLACK) === them) out.push(encode(sq, to, 0, 0));
            break;
          }
        }
      }
    }
    return out;
  };

  Position.prototype.genCastles = function (sq, out) {
    var b = this.b, us = this.turn, them = us ^ BLACK, base = us ? 56 : 0;
    if (sq !== base + 4) return;
    var kSide = us ? 4 : 1, qSide = us ? 8 : 2;
    if (this.castle & kSide && !b[base + 5] && !b[base + 6] && b[base + 7] === (us | ROOK) &&
        !this.attacked(base + 4, them) && !this.attacked(base + 5, them) && !this.attacked(base + 6, them))
      out.push(encode(base + 4, base + 6, 0, F_CASTLE));
    if (this.castle & qSide && !b[base + 3] && !b[base + 2] && !b[base + 1] && b[base] === (us | ROOK) &&
        !this.attacked(base + 4, them) && !this.attacked(base + 3, them) && !this.attacked(base + 2, them))
      out.push(encode(base + 4, base + 2, 0, F_CASTLE));
  };

  Position.prototype.make = function (m) {
    var b = this.b, from = mFrom(m), to = mTo(m), promo = mPromo(m), flag = mFlag(m);
    var piece = b[from], us = piece & BLACK, captured = b[to];
    this.stack.push(m, captured, this.castle, this.ep, this.half);
    if (flag === F_EP) {
      var capSq = to + (us ? 8 : -8);
      captured = b[capSq]; b[capSq] = 0;
      this.stack[this.stack.length - 4] = captured;
    }
    b[to] = promo ? (us | promo) : piece;
    b[from] = 0;
    if (flag === F_CASTLE) {
      if (to > from) { b[from + 1] = b[from + 3]; b[from + 3] = 0; }
      else { b[from - 1] = b[from - 4]; b[from - 4] = 0; }
    }
    if ((piece & 7) === KING) this.kings[us] = to;
    this.castle &= CASTLE_MASK[from] & CASTLE_MASK[to];
    this.ep = flag === F_DOUBLE ? (from + to) >> 1 : -1;
    this.half = ((piece & 7) === PAWN || captured) ? 0 : this.half + 1;
    if (us) this.full++;
    this.turn ^= BLACK;
  };

  Position.prototype.unmake = function () {
    var st = this.stack, n = st.length;
    var half = st[n - 1], ep = st[n - 2], castle = st[n - 3], captured = st[n - 4], m = st[n - 5];
    st.length = n - 5;
    var b = this.b, from = mFrom(m), to = mTo(m), promo = mPromo(m), flag = mFlag(m);
    this.turn ^= BLACK;
    var us = this.turn, piece = promo ? (us | PAWN) : b[to];
    b[from] = piece;
    if (flag === F_EP) { b[to] = 0; b[to + (us ? 8 : -8)] = captured; }
    else b[to] = captured;
    if (flag === F_CASTLE) {
      if (to > from) { b[from + 3] = b[from + 1]; b[from + 1] = 0; }
      else { b[from - 4] = b[from - 1]; b[from - 1] = 0; }
    }
    if ((piece & 7) === KING) this.kings[us] = from;
    this.castle = castle; this.ep = ep; this.half = half;
    if (us) this.full--;
  };

  Position.prototype.legal = function () {
    var moves = this.gen(false), out = [], us = this.turn;
    for (var i = 0; i < moves.length; i++) {
      this.make(moves[i]);
      if (!this.inCheck(us)) out.push(moves[i]);
      this.unmake();
    }
    return out;
  };

  Position.prototype.perft = function (depth) {
    if (depth === 0) return 1;
    var moves = this.gen(false), n = 0, us = this.turn;
    for (var i = 0; i < moves.length; i++) {
      this.make(moves[i]);
      if (!this.inCheck(us)) n += this.perft(depth - 1);
      this.unmake();
    }
    return n;
  };

  Position.prototype.insufficient = function () {
    var minors = [], b = this.b;
    for (var sq = 0; sq < 64; sq++) {
      var t = b[sq] & 7;
      if (!t || t === KING) continue;
      if (t === PAWN || t === ROOK || t === QUEEN) return false;
      minors.push({ t: t, sq: sq, c: b[sq] & BLACK });
    }
    if (minors.length <= 1) return true;
    // Only bishops, all on the same square color.
    var shade = ((minors[0].sq >> 3) + minors[0].sq) & 1;
    for (var i = 0; i < minors.length; i++)
      if (minors[i].t !== BISHOP || (((minors[i].sq >> 3) + minors[i].sq) & 1) !== shade) return false;
    return true;
  };

  function uci(m) {
    var p = mPromo(m);
    return sqName(mFrom(m)) + sqName(mTo(m)) + (p ? LETTERS[p] : '');
  }

  Position.prototype.san = function (m, legalMoves) {
    var from = mFrom(m), to = mTo(m), piece = this.b[from], t = piece & 7, s;
    if (mFlag(m) === F_CASTLE) s = to > from ? 'O-O' : 'O-O-O';
    else {
      var capture = this.b[to] || mFlag(m) === F_EP;
      if (t === PAWN) {
        s = (capture ? FILES[from & 7] + 'x' : '') + sqName(to);
        if (mPromo(m)) s += '=' + LETTERS[mPromo(m)].toUpperCase();
      } else {
        var sameFile = false, sameRank = false, ambiguous = false;
        for (var i = 0; i < legalMoves.length; i++) {
          var o = legalMoves[i], of = mFrom(o);
          if (o === m || mTo(o) !== to || of === from || this.b[of] !== piece) continue;
          ambiguous = true;
          if ((of & 7) === (from & 7)) sameFile = true;
          if ((of >> 3) === (from >> 3)) sameRank = true;
        }
        var dis = '';
        if (ambiguous) dis = !sameFile ? FILES[from & 7] : !sameRank ? String((from >> 3) + 1) : sqName(from);
        s = LETTERS[t].toUpperCase() + dis + (capture ? 'x' : '') + sqName(to);
      }
    }
    this.make(m);
    if (this.inCheck()) s += this.legal().length ? '+' : '#';
    this.unmake();
    return s;
  };

  // ---------------------------------------------------------------- evaluation

  var VALUE = [0, 100, 320, 330, 500, 900, 0];
  // Piece-square tables from White's side, rank 8 first (index = (7 - rank) * 8 + file).
  var PST = [null,
    [0, 0, 0, 0, 0, 0, 0, 0, 50, 50, 50, 50, 50, 50, 50, 50, 10, 10, 20, 30, 30, 20, 10, 10, 5, 5, 10, 25, 25, 10, 5, 5,
     0, 0, 0, 20, 20, 0, 0, 0, 5, -5, -10, 0, 0, -10, -5, 5, 5, 10, 10, -20, -20, 10, 10, 5, 0, 0, 0, 0, 0, 0, 0, 0],
    [-50, -40, -30, -30, -30, -30, -40, -50, -40, -20, 0, 0, 0, 0, -20, -40, -30, 0, 10, 15, 15, 10, 0, -30, -30, 5, 15, 20, 20, 15, 5, -30,
     -30, 0, 15, 20, 20, 15, 0, -30, -30, 5, 10, 15, 15, 10, 5, -30, -40, -20, 0, 5, 5, 0, -20, -40, -50, -40, -30, -30, -30, -30, -40, -50],
    [-20, -10, -10, -10, -10, -10, -10, -20, -10, 0, 0, 0, 0, 0, 0, -10, -10, 0, 5, 10, 10, 5, 0, -10, -10, 5, 5, 10, 10, 5, 5, -10,
     -10, 0, 10, 10, 10, 10, 0, -10, -10, 10, 10, 10, 10, 10, 10, -10, -10, 5, 0, 0, 0, 0, 5, -10, -20, -10, -10, -10, -10, -10, -10, -20],
    [0, 0, 0, 0, 0, 0, 0, 0, 5, 10, 10, 10, 10, 10, 10, 5, -5, 0, 0, 0, 0, 0, 0, -5, -5, 0, 0, 0, 0, 0, 0, -5,
     -5, 0, 0, 0, 0, 0, 0, -5, -5, 0, 0, 0, 0, 0, 0, -5, -5, 0, 0, 0, 0, 0, 0, -5, 0, 0, 0, 5, 5, 0, 0, 0],
    [-20, -10, -10, -5, -5, -10, -10, -20, -10, 0, 0, 0, 0, 0, 0, -10, -10, 0, 5, 5, 5, 5, 0, -10, -5, 0, 5, 5, 5, 5, 0, -5,
     0, 0, 5, 5, 5, 5, 0, -5, -10, 5, 5, 5, 5, 5, 0, -10, -10, 0, 5, 0, 0, 0, 0, -10, -20, -10, -10, -5, -5, -10, -10, -20],
    [-30, -40, -40, -50, -50, -40, -40, -30, -30, -40, -40, -50, -50, -40, -40, -30, -30, -40, -40, -50, -50, -40, -40, -30, -30, -40, -40, -50, -50, -40, -40, -30,
     -20, -30, -30, -40, -40, -30, -30, -20, -10, -20, -20, -20, -20, -20, -20, -10, 20, 20, 0, 0, 0, 0, 20, 20, 20, 30, 10, 0, 0, 10, 30, 20]];
  var KING_END = [-50, -40, -30, -20, -20, -30, -40, -50, -30, -20, -10, 0, 0, -10, -20, -30, -30, -10, 20, 30, 30, 20, -10, -30, -30, -10, 30, 40, 40, 30, -10, -30,
    -30, -10, 30, 40, 40, 30, -10, -30, -30, -10, 20, 30, 30, 20, -10, -30, -30, -30, 0, 0, 0, 0, -30, -30, -50, -30, -30, -30, -30, -30, -30, -50];

  function pstIndex(sq, color) { return color ? sq : (7 - (sq >> 3)) * 8 + (sq & 7); }

  Position.prototype.evaluate = function () {
    var b = this.b, score = 0, nonPawn = 0, sq, p;
    for (sq = 0; sq < 64; sq++) { p = b[sq] & 7; if (p > PAWN && p < KING) nonPawn += VALUE[p]; }
    var endgame = nonPawn <= 1300;
    for (sq = 0; sq < 64; sq++) {
      p = b[sq];
      if (!p) continue;
      var t = p & 7, c = p & BLACK, idx = pstIndex(sq, c);
      var v = VALUE[t] + (t === KING && endgame ? KING_END[idx] : PST[t][idx]);
      score += c ? -v : v;
    }
    return this.turn ? -score : score;
  };

  // ---------------------------------------------------------------- search

  function Searcher(pos, opts) {
    this.pos = pos;
    this.deadline = Date.now() + (opts.timeMs || 2000);
    this.maxDepth = opts.depth || 4;
    this.quiesce = opts.quiesce !== false;
    this.noise = opts.noise || 0;
    this.nodes = 0;
    this.stopped = false;
    this.killers = [];
  }

  Searcher.prototype.order = function (moves, ply, pvMove) {
    var b = this.pos.b, k = this.killers[ply] || [], scored = [];
    for (var i = 0; i < moves.length; i++) {
      var m = moves[i], s = 0, victim = b[mTo(m)] & 7;
      if (m === pvMove) s = 1e6;
      else if (victim) s = 1e5 + VALUE[victim] * 10 - VALUE[b[mFrom(m)] & 7] / 10;
      else if (mFlag(m) === F_EP) s = 1e5 + 1000;
      else if (mPromo(m)) s = 9e4 + VALUE[mPromo(m)];
      else if (m === k[0]) s = 8e4;
      else if (m === k[1]) s = 7e4;
      scored.push([s, m]);
    }
    scored.sort(function (a, c) { return c[0] - a[0]; });
    for (i = 0; i < scored.length; i++) moves[i] = scored[i][1];
    return moves;
  };

  Searcher.prototype.tick = function () {
    if ((++this.nodes & 2047) === 0 && Date.now() > this.deadline) this.stopped = true;
  };

  Searcher.prototype.qs = function (alpha, beta, ply) {
    this.tick();
    var pos = this.pos, stand = pos.evaluate();
    if (stand >= beta) return stand;
    if (stand > alpha) alpha = stand;
    if (ply > 40) return stand;
    var moves = this.order(pos.gen(true), ply, 0), us = pos.turn;
    for (var i = 0; i < moves.length; i++) {
      pos.make(moves[i]);
      if (pos.inCheck(us)) { pos.unmake(); continue; }
      var score = -this.qs(-beta, -alpha, ply + 1);
      pos.unmake();
      if (this.stopped) return 0;
      if (score >= beta) return score;
      if (score > alpha) alpha = score;
    }
    return alpha;
  };

  Searcher.prototype.search = function (depth, alpha, beta, ply) {
    var pos = this.pos, us = pos.turn, check = pos.inCheck(us);
    if (check && ply < 20) depth++;
    if (depth <= 0) return this.quiesce ? this.qs(alpha, beta, ply) : pos.evaluate();
    this.tick();
    if (ply > 0 && pos.half >= 100) return 0;
    var moves = this.order(pos.gen(false), ply, 0), legal = 0, best = -INF;
    for (var i = 0; i < moves.length; i++) {
      var m = moves[i];
      pos.make(m);
      if (pos.inCheck(us)) { pos.unmake(); continue; }
      legal++;
      var score = -this.search(depth - 1, -beta, -alpha, ply + 1);
      pos.unmake();
      if (this.stopped) return 0;
      if (score > best) best = score;
      if (score > alpha) alpha = score;
      if (alpha >= beta) {
        if (!pos.b[mTo(m)]) {
          var k = this.killers[ply] || (this.killers[ply] = [0, 0]);
          if (k[0] !== m) { k[1] = k[0]; k[0] = m; }
        }
        break;
      }
    }
    if (!legal) return check ? -MATE + ply : 0;
    return best;
  };

  // Iterative deepening at the root. Returns the chosen move (with optional noise for weaker levels).
  Searcher.prototype.run = function () {
    var pos = this.pos, us = pos.turn, roots = [], i;
    var moves = pos.legal();
    if (!moves.length) return 0;
    for (i = 0; i < moves.length; i++) roots.push({ m: moves[i], score: 0 });
    var completed = null;
    for (var depth = 1; depth <= this.maxDepth; depth++) {
      var alpha = -INF;
      for (i = 0; i < roots.length; i++) {
        pos.make(roots[i].m);
        // Full window per root move so every move has an exact score for the noise step.
        var score = -this.search(depth - 1, -INF, this.noise ? INF : -alpha, 1);
        pos.unmake();
        if (this.stopped) break;
        roots[i].score = score;
        if (score > alpha) alpha = score;
      }
      if (this.stopped) break;
      roots.sort(function (a, c) { return c.score - a.score; });
      completed = roots.map(function (r) { return { m: r.m, score: r.score }; });
      if (roots[0].score >= MATE - 100) break;
    }
    if (!completed) completed = roots;
    if (!this.noise) return completed[0].m;
    var noise = this.noise, best = null;
    for (i = 0; i < completed.length; i++) {
      var noisy = completed[i].score + (Math.random() * 2 - 1) * noise;
      // Never throw away a forced mate.
      if (completed[i].score >= MATE - 100) noisy += 1e6;
      if (!best || noisy > best.v) best = { v: noisy, m: completed[i].m };
    }
    return best.m;
  };

  var LEVELS = {
    easy: { depth: 1, timeMs: 600, noise: 140 },
    medium: { depth: 3, timeMs: 1500, noise: 25 },
    hard: { depth: 7, timeMs: 2500, noise: 0 }
  };

  function bestMove(fen, level) {
    var pos = new Position(fen);
    var m = new Searcher(pos, LEVELS[level] || LEVELS.medium).run();
    return m ? uci(m) : null;
  }

  // Worker entry: { fen, level } -> { move }
  if (typeof window === 'undefined' && typeof self !== 'undefined' && typeof importScripts === 'function') {
    self.onmessage = function (e) {
      self.postMessage({ id: e.data.id, move: bestMove(e.data.fen, e.data.level) });
    };
  }

  return {
    Position: Position, PAWN: PAWN, KNIGHT: KNIGHT, BISHOP: BISHOP, ROOK: ROOK, QUEEN: QUEEN, KING: KING,
    WHITE: WHITE, BLACK: BLACK, F_EP: F_EP, F_CASTLE: F_CASTLE,
    from: mFrom, to: mTo, promo: mPromo, flag: mFlag, uci: uci, sqName: sqName, sqParse: sqParse,
    bestMove: bestMove
  };
})();
