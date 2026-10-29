// Blackjack with a player who can see the next card off the shoe, the dealer's hole card, or both.
// usage: node superpower.js <power: next|hole|both> <seats: 1|4> <seat index 0-based> <rounds> [firstbet|plausible:<delta>]
// plausible:<delta> disguises the play: the player only deviates to an action whose ordinary (no-power)
// EV is within <delta> of the basic-strategy best, so every play looks like one a normal player might make.
const fs = require('fs');
const html = fs.readFileSync(require('path').join(__dirname, 'blackjack.html'), 'utf8');
const engine = html.slice(html.indexOf("'use strict';"), html.indexOf('function fmtPct'));
eval(engine + '\nglobalThis.bs = basicStrategy; globalThis.handTotal = handTotal; globalThis.mkA = makeAnalyzer;');
const S = { h17: false, das: true, surrender: true, resplitAces: false, bjPays: 1.5, decks: 6, penetration: 0.75 };
const [power, seatsArg, seatArg, roundsArg, extra] = process.argv.slice(2);
const firstbet = extra === 'firstbet';
const delta = extra && extra.startsWith('plausible:') ? +extra.split(':')[1] : null;

const SEATS = +seatsArg || 1, ME = +seatArg || 0, N = +roundsArg || 20000;
const seesNext = power === 'next' || power === 'both', seesHole = power === 'hole' || power === 'both';
const atEnd = ME === SEATS - 1;   // the card after my stand goes to the dealer
const RANK = ['', 'A', '2', '3', '4', '5', '6', '7', '8', '9', '10'];
const card = v => ({ rank: RANK[v], suit: '♠' });
const total = vals => handTotal(vals.map(card));

let shoe = [], counts = new Array(11).fill(0), cut = 0;
function shuffle() {
  shoe = [];
  for (let d = 0; d < S.decks; d++) for (let v = 1; v <= 10; v++) for (let k = 0; k < (v === 10 ? 16 : 4); k++) shoe.push(v);
  for (let i = shoe.length - 1; i > 0; i--) { const j = Math.floor(Math.random() * (i + 1)); [shoe[i], shoe[j]] = [shoe[j], shoe[i]]; }
  counts.fill(0); for (const v of shoe) counts[v]++;
  cut = Math.floor(shoe.length * (1 - S.penetration));
}
const draw = () => { const v = shoe.pop(); counts[v]--; return v; };
const peekNext = () => shoe[shoe.length - 1];
function probsUnseen(hole) { const c = counts.slice(); if (hole && !seesHole) c[hole]++; const n = c.reduce((a, b) => a + b, 0); return c.map(x => x / n); }
function probsInnocent(hole) { const c = counts.slice(); if (hole) c[hole]++; const n = c.reduce((a, b) => a + b, 0); return c.map(x => x / n); }

// Analyzer for a player with extra information. p: rank probabilities of the unseen cards.
function makePowerAnalyzer(p) {
  const nxt = (t, soft, c) => { if (c === 1 && t + 11 <= 21) return [t + 11, true]; let x = t + c, s = soft; if (x > 21 && s) { x -= 10; s = false; } return [x, s]; };
  const stands = (t, soft) => t > 17 || (t === 17 && !(soft && S.h17));
  const outcome = t => { const d = [0, 0, 0, 0, 0, 0]; if (t > 21) d[5] = 1; else d[t - 17] = 1; return d; };
  const fromMemo = new Map();
  function dealerFrom(t, soft) {   // random draws from here
    if (t > 21 || stands(t, soft)) return outcome(t);
    const k = t * 2 + (soft ? 1 : 0); if (fromMemo.has(k)) return fromMemo.get(k);
    const d = [0, 0, 0, 0, 0, 0];
    for (let c = 1; c <= 10; c++) { if (!p[c]) continue; const [t2, s2] = nxt(t, soft, c), sub = dealerFrom(t2, s2); for (let i = 0; i < 6; i++) d[i] += p[c] * sub[i]; }
    fromMemo.set(k, d); return d;
  }
  const distMemo = new Map();
  // Dealer's final distribution given known dealer cards (up, or up+hole) and, if known, the
  // dealer's first draw. With only the up card, the hole is conditioned on the no-blackjack peek.
  function dealerDist(known, firstDraw) {
    const k = known.join(',') + '|' + (firstDraw || 0); if (distMemo.has(k)) return distMemo.get(k);
    const afterHole = (t, soft) => {
      if (stands(t, soft)) return outcome(t);
      if (firstDraw) { const [t2, s2] = nxt(t, soft, firstDraw); return dealerFrom(t2, s2); }
      return dealerFrom(t, soft);
    };
    let d;
    if (known.length === 2) { const [t1, s1] = nxt(0, false, known[0]); const [t2, s2] = nxt(t1, s1, known[1]); d = afterHole(t2, s2); }
    else {
      const up = known[0], [t1, s1] = nxt(0, false, up), excl = up === 1 ? 10 : up === 10 ? 1 : 0, norm = 1 - (excl ? p[excl] : 0);
      d = [0, 0, 0, 0, 0, 0];
      for (let h = 1; h <= 10; h++) { if (h === excl || !p[h]) continue; const [t2, s2] = nxt(t1, s1, h), sub = afterHole(t2, s2); for (let i = 0; i < 6; i++) d[i] += p[h] / norm * sub[i]; }
    }
    distMemo.set(k, d); return d;
  }
  const standEV = (t, dd) => { if (t > 21) return -1; let ev = dd[5]; for (let i = 0; i < 5; i++) { const d = 17 + i; ev += dd[i] * (t > d ? 1 : t < d ? -1 : 0); } return ev; };
  // Value of (t, soft) when the next card is unknown and only hit/stand remain.
  const hsMemo = new Map();
  function hs(t, soft, known) {
    const k = known.join(',') + '|' + t * 2 + (soft ? 1 : 0); if (hsMemo.has(k)) return hsMemo.get(k);
    const dd = dealerDist(known, null);
    let best = standEV(t, dd);
    if (t < 21) { let hit = 0; for (let c = 1; c <= 10; c++) { if (!p[c]) continue; const [t2, s2] = nxt(t, soft, c); hit += p[c] * (t2 > 21 ? -1 : hs(t2, s2, known)); } best = Math.max(best, hit); }
    hsMemo.set(k, best); return best;
  }
  // Value of (t, soft) when the player will see each next card before deciding (hit/stand only).
  const vMemo = new Map();
  function V(t, soft, known) {
    if (t >= 21) return standEV(t, dealerDist(known, null));
    const k = known.join(',') + '|' + t * 2 + (soft ? 1 : 0); if (vMemo.has(k)) return vMemo.get(k);
    let v = 0;
    for (let c = 1; c <= 10; c++) { if (!p[c]) continue; v += p[c] * Math.max(standGiven(t, known, c), hitGiven(t, soft, known, c)); }
    vMemo.set(k, v); return v;
  }
  const standGiven = (t, known, c) => standEV(t, dealerDist(known, atEnd ? c : null));
  const hitGiven = (t, soft, known, c) => { const [t2, s2] = nxt(t, soft, c); return t2 > 21 ? -1 : V(t2, s2, known); };
  // EVs of the options at an actual decision. known: dealer cards I can see; c: next card if I can see it.
  function actions(t, soft, pairVal, known, c, opts) {
    const dd0 = dealerDist(known, null);
    const out = {};
    out.S = c ? standGiven(t, known, c) : standEV(t, dd0);
    if (opts.canHit !== false) {
      if (c) out.H = hitGiven(t, soft, known, c);
      else { let h = 0; for (let x = 1; x <= 10; x++) { if (!p[x]) continue; const [t2, s2] = nxt(t, soft, x); h += p[x] * (t2 > 21 ? -1 : (seesNext ? V(t2, s2, known) : hs(t2, s2, known))); } out.H = h; }
    }
    if (opts.canDouble) {
      if (c) { const [t2] = nxt(t, soft, c); out.D = 2 * standEV(t2, dd0); }
      else { let d = 0; for (let x = 1; x <= 10; x++) { if (!p[x]) continue; const [t2] = nxt(t, soft, x); d += p[x] * 2 * standEV(t2, dd0); } out.D = d; }
    }
    if (opts.canSplit && pairVal) {
      // first hand gets c if known; later cards unknown; no re-splits (a lower bound on the split's value)
      const [t1, s1] = nxt(0, false, pairVal);
      const handVal = x => { const [t2, s2] = nxt(t1, s1, x); if (pairVal === 1) return standEV(t2, dd0); let v = seesNext ? V(t2, s2, known) : hs(t2, s2, known); if (S.das) { let d = 0; for (let y = 1; y <= 10; y++) { if (!p[y]) continue; const [t3] = nxt(t2, s2, y); d += p[y] * 2 * standEV(t3, dd0); } v = Math.max(v, d); } return v; };
      let rest = 0; for (let x = 1; x <= 10; x++) if (p[x]) rest += p[x] * handVal(x);
      out.P = (c ? handVal(c) : rest) + rest;
    }
    if (opts.canSurrender) out.R = -0.5;
    return out;
  }
  return { actions };
}

let net = 0, sq = 0, wagered = 0, decisions = 0, differs = 0;
shuffle();
const t0 = Date.now();
for (let r = 0; r < N; r++) {
  if (shoe.length <= cut) shuffle();
  const bet = firstbet && seesNext && ME === 0 ? ((peekNext() === 1 || peekNext() === 10) ? 8 : 1) : 1;
  const players = [];
  for (let s = 0; s < SEATS; s++) players.push({ hands: [{ cards: [draw()], bet: 1, fromSplit: false, splitAces: false, done: false, bust: false, surrendered: false }] });
  const up = draw();
  for (const pl of players) pl.hands[0].cards.push(draw());
  const hole = draw();
  const dealerBJ = (up === 1 && hole === 10) || (up === 10 && hole === 1);
  let myNet = 0;
  const me = players[ME];
  if (up === 1) {   // insurance for me only
    const take = seesHole && delta === null ? hole === 10 : probsInnocent(hole)[10] > 1 / 3;   // a disguised player cannot take insurance only when it hits
    if (take) myNet += dealerBJ ? 1 : -0.5;
  }
  const myBJ = me.hands[0].cards[0] + me.hands[0].cards[1] === 11 && me.hands[0].cards.includes(1);
  if (dealerBJ) myNet += myBJ ? 0 : -1;
  else if (myBJ) myNet += S.bjPays;
  else {
    for (let s = 0; s < SEATS; s++) {
      const pl = players[s], isMe = s === ME;
      const hands = pl.hands;
      if (!isMe && hands[0].cards.includes(1) && hands[0].cards[0] + hands[0].cards[1] === 11) continue;   // other player's blackjack
      for (let i = 0; i < hands.length; i++) {
        const h = hands[i];
        while (!h.done) {
          const two = h.cards.length === 2;
          const opts = { canHit: !h.splitAces, canDouble: two && !h.splitAces && (!h.fromSplit || S.das),
            canSplit: two && h.cards[0] === h.cards[1] && hands.length < 4 && !(h.cards[0] === 1 && h.fromSplit && !S.resplitAces),
            canSurrender: S.surrender && two && !h.fromSplit && hands.length === 1 };
          let a;
          if (h.splitAces) a = 'S';
          else if (!isMe) a = bs(h.cards.map(card), card(up), S, opts);
          else {
            const { total: t, soft } = total(h.cards);
            const pairVal = opts.canSplit && h.cards[0] === h.cards[1] ? h.cards[0] : 0;
            const known = seesHole ? [up, hole] : [up];
            const c = seesNext ? peekNext() : 0;
            const evs = makePowerAnalyzer(probsUnseen(hole)).actions(t, soft, pairVal, known, c, Object.assign({}, opts, { canSplit: !!pairVal }));
            if (delta !== null) {   // disguise: restrict to plays that look ordinary
              const plain = mkA(probsInnocent(hole), S).actions(t, soft, pairVal, up, Object.assign({}, opts, { canSplit: !!pairVal }));
              const top = Math.max(...Object.values(plain));
              for (const k of Object.keys(evs)) if (plain[k] === undefined || plain[k] < top - delta) delete evs[k];
            }
            a = Object.keys(evs).reduce((b, k) => (evs[k] > evs[b] ? k : b));
            decisions++; if (a !== bs(h.cards.map(card), card(up), S, opts)) differs++;
          }
          if (a === 'H') { h.cards.push(draw()); const t = total(h.cards).total; if (t > 21) { h.bust = true; h.done = true; } else if (t === 21) h.done = true; }
          else if (a === 'S') h.done = true;
          else if (a === 'D') { h.bet = 2; h.cards.push(draw()); if (total(h.cards).total > 21) h.bust = true; h.done = true; }
          else if (a === 'R') { h.surrendered = true; h.done = true; }
          else if (a === 'P') {
            const aces = h.cards[0] === 1;
            const h2 = { cards: [h.cards[1]], bet: 1, fromSplit: true, splitAces: aces, done: false, bust: false, surrendered: false };
            h.cards = [h.cards[0]]; h.fromSplit = true; h.splitAces = aces;
            hands.splice(i + 1, 0, h2);
            h.cards.push(draw()); h2.cards.push(draw());
            if (aces) { h.done = true; h2.done = true; }
          }
        }
      }
    }
    const dealer = [up, hole];
    const anyLive = players.some(pl => pl.hands.some(h => !h.bust && !h.surrendered));
    if (anyLive) for (;;) { const { total: t, soft } = total(dealer); if (t > 17 || (t === 17 && !(soft && S.h17))) break; dealer.push(draw()); }
    const d = total(dealer).total;
    for (const h of me.hands) {
      if (h.surrendered) { myNet -= 0.5; continue; }
      const t = total(h.cards).total;
      if (h.bust) myNet -= h.bet; else if (d > 21 || t > d) myNet += h.bet; else if (t < d) myNet -= h.bet;
    }
  }
  const x = myNet * bet; net += x; sq += x * x; wagered += bet;
}
const secs = (Date.now() - t0) / 1000, per = net / N, sd = Math.sqrt(sq / N - per * per), se = sd / Math.sqrt(N);
const label = `${power}${firstbet ? '+firstbet' : ''}${delta !== null ? ' disguised δ=' + delta : ''}, ${SEATS === 1 ? 'heads-up' : `seat ${ME + 1} of ${SEATS}`}`;
console.log(`${label.padEnd(34)} edge ${(100 * net / wagered).toFixed(2).padStart(7)}% ± ${(100 * se * N / wagered).toFixed(2)} | per round ${(100 * per).toFixed(2).padStart(7)}% | decisions differing from basic strategy ${(100 * differs / decisions).toFixed(1)}% | ${N} rounds, ${secs.toFixed(0)} s`);
fs.appendFileSync(require('path').join(__dirname, 'sim-superpower.jsonl'), JSON.stringify({ power, seats: SEATS, seat: ME, firstbet: !!firstbet, delta, edge: +(100 * net / wagered).toFixed(2), se: +(100 * se * N / wagered).toFixed(2), perRound: +(100 * per).toFixed(2), differs: +(100 * differs / decisions).toFixed(1), rounds: N }) + '\n');
