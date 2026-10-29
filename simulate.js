// Heads-up blackjack simulation of four players under the trainer's default rules:
//   basic    basic strategy, flat bet
//   hilo     basic strategy + Illustrious 18 / Fab 4 index plays, bets from the Hi-Lo true count
//   acefive  basic strategy, bets from the Ace-Five count (double the last bet at +2 or more)
//   perfect  knows the exact remaining composition, plays by EV, bets from the computed edge
// usage: node simulate.js <mode> <rounds>   (reads the game engine out of blackjack.html next to it)
const fs = require('fs');
const html = fs.readFileSync(require('path').join(__dirname, 'blackjack.html'), 'utf8');
const engine = html.slice(html.indexOf("'use strict';"), html.indexOf('function fmtPct'));
eval(engine + '\nglobalThis.bs = basicStrategy; globalThis.dev = deviation; globalThis.handTotal = handTotal; globalThis.mkA = makeAnalyzer;');
const S = { h17: false, das: true, surrender: true, resplitAces: false, bjPays: 1.5, decks: 6, penetration: 0.75 };
const mode = process.argv[2] || 'basic', N = +process.argv[3] || 20000;
const RANK = ['', 'A', '2', '3', '4', '5', '6', '7', '8', '9', '10'];
const card = v => ({ rank: RANK[v], suit: '♠' });
const hiLoOf = v => (v >= 2 && v <= 6 ? 1 : v >= 7 && v <= 9 ? 0 : -1);
const aceFiveOf = v => (v === 5 ? 1 : v === 1 ? -1 : 0);

let shoe = [], counts = new Array(11).fill(0), cut = 0, rc = 0, af = 0;
function shuffle() {
  shoe = [];
  for (let d = 0; d < S.decks; d++) for (let v = 1; v <= 10; v++) for (let k = 0; k < (v === 10 ? 16 : 4); k++) shoe.push(v);
  for (let i = shoe.length - 1; i > 0; i--) { const j = Math.floor(Math.random() * (i + 1)); [shoe[i], shoe[j]] = [shoe[j], shoe[i]]; }
  counts.fill(0); for (const v of shoe) counts[v]++;
  cut = Math.floor(shoe.length * (1 - S.penetration));
  rc = 0; af = 0;
}
// `seen` cards update the counts; the hole card is drawn unseen and counted when revealed
const draw = (seen = true) => { const v = shoe.pop(); counts[v]--; if (seen) { rc += hiLoOf(v); af += aceFiveOf(v); } return v; };
const reveal = v => { rc += hiLoOf(v); af += aceFiveOf(v); };
function probsUnseen(hole) { const c = counts.slice(); if (hole) c[hole]++; const n = c.reduce((a, b) => a + b, 0); return c.map(x => x / n); }
const trueCount = hole => rc / ((shoe.length + (hole ? 1 : 0)) / 52);
const total = vals => handTotal(vals.map(card));

// --- betting schemes, each a function of the player's pre-deal information; `st` holds per-scheme state
const clampU = (u, max) => Math.min(max, Math.max(1, u));
const hiloRamp = max => (info, st) => clampU(Math.pow(2, Math.floor(info.tc) - 1), max);   // 1 unit below TC +2, then 2, 4, 8, 16 at +2, +3, +4, +5
const aceFiveRamp = max => (info, st) => { const b = info.af >= 2 ? Math.min(max, 2 * (st.last || 1)) : 1; st.last = b; return b; };
const edgeRamp = max => (info, st) => (info.edge <= 0 ? 1 : clampU(Math.round(info.edge * 100 * max / 1.5), max));   // max units at +1.5% edge
const SCHEMES = {
  basic: { 'flat 1 unit': () => 1 },
  hilo: { 'flat 1 unit': () => 1, 'spread 1–4': hiloRamp(4), 'spread 1–8': hiloRamp(8), 'spread 1–16': hiloRamp(16),
          'spread 1–8, sit out at TC < 0': (i, st) => (i.tc < 0 ? 0 : hiloRamp(8)(i, st)) },
  acefive: { 'flat 1 unit': () => 1, 'spread 1–4': aceFiveRamp(4), 'spread 1–8': aceFiveRamp(8), 'spread 1–16': aceFiveRamp(16) },
  perfect: { 'flat 1 unit': () => 1, 'spread 1–4': edgeRamp(4), 'spread 1–8': edgeRamp(8), 'spread 1–16': edgeRamp(16),
             'spread 1–8, sit out when edge < 0': (i, st) => (i.edge < 0 ? 0 : edgeRamp(8)(i, st)) },
}[mode];

function decide(vals, up, hole, opts) {
  const cards = vals.map(card), upc = card(up);
  if (mode === 'basic' || mode === 'acefive') return bs(cards, upc, S, opts);
  if (mode === 'hilo') { const d = dev(cards, upc, trueCount(hole), S, opts); return d || bs(cards, upc, S, opts); }
  const { total: t, soft } = total(vals);
  const pairVal = opts.canSplit && vals.length === 2 && vals[0] === vals[1] ? vals[0] : 0;
  const evs = mkA(probsUnseen(hole), S).actions(t, soft, pairVal, up, Object.assign({}, opts, { canSplit: !!pairVal }));
  return Object.keys(evs).reduce((b, k) => (evs[k] > evs[b] ? k : b));
}
function takeInsurance(hole) {
  if (mode === 'hilo') return trueCount(hole) >= 3;
  if (mode === 'perfect') return probsUnseen(hole)[10] > 1 / 3;
  return false;
}

const res = {}, st = {};
for (const k in SCHEMES) { res[k] = { net: 0, sq: 0, wagered: 0, rounds: 0 }; st[k] = {}; }
let posRounds = 0;
shuffle();
const t0 = Date.now();
for (let r = 0; r < N; r++) {
  if (shoe.length <= cut) shuffle();
  const info = { tc: mode === 'hilo' ? trueCount(0) : 0, af, edge: mode === 'perfect' ? mkA(probsUnseen(0), S).roundEV() : 0 };
  if ((mode === 'perfect' && info.edge > 0) || (mode === 'hilo' && info.tc >= 2)) posRounds++;
  const bets = {}; for (const k in SCHEMES) bets[k] = SCHEMES[k](info, st[k]);
  let net = 0;
  if (Object.values(bets).some(b => b > 0)) {
    const p1 = draw(), up = draw(), p2 = draw(), hole = draw(false);
    const dealerBJ = (up === 1 && hole === 10) || (up === 10 && hole === 1);
    if (up === 1 && takeInsurance(hole)) net += dealerBJ ? 1 : -0.5;
    const playerBJ = (p1 === 1 && p2 === 10) || (p1 === 10 && p2 === 1);
    if (dealerBJ) net += playerBJ ? 0 : -1;
    else if (playerBJ) net += S.bjPays;
    else {
      const hands = [{ cards: [p1, p2], bet: 1, fromSplit: false, splitAces: false, done: false, bust: false, surrendered: false }];
      for (let i = 0; i < hands.length; i++) {
        const h = hands[i];
        while (!h.done) {
          const two = h.cards.length === 2;
          const opts = { canHit: !h.splitAces, canDouble: two && !h.splitAces && (!h.fromSplit || S.das),
            canSplit: two && h.cards[0] === h.cards[1] && hands.length < 4 && !(h.cards[0] === 1 && h.fromSplit && !S.resplitAces),
            canSurrender: S.surrender && two && !h.fromSplit && hands.length === 1 };
          const a = h.splitAces ? 'S' : decide(h.cards, up, hole, opts);
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
      const dealer = [up, hole];
      if (hands.some(h => !h.bust && !h.surrendered)) {
        for (;;) { const { total: t, soft } = total(dealer); if (t > 17 || (t === 17 && !(soft && S.h17))) break; dealer.push(draw()); }
      }
      const d = total(dealer).total;
      for (const h of hands) {
        if (h.surrendered) { net -= 0.5; continue; }
        const t = total(h.cards).total;
        if (h.bust) net -= h.bet; else if (d > 21 || t > d) net += h.bet; else if (t < d) net -= h.bet;
      }
    }
    reveal(hole);
  }
  for (const k in SCHEMES) { const x = net * bets[k]; res[k].net += x; res[k].sq += x * x; res[k].wagered += bets[k]; res[k].rounds++; }
}
const secs = (Date.now() - t0) / 1000;
console.log(`${mode}: ${N} rounds in ${secs.toFixed(0)} s. Rules: 6D S17 DAS LS, 75% penetration, 3:2, heads-up.`);
if (mode !== 'basic' && mode !== 'acefive') console.log(`Rounds with ${mode === 'perfect' ? 'a positive edge' : 'TC ≥ +2'}: ${(100 * posRounds / N).toFixed(1)}%.`);
const out = [];
for (const k in res) {
  const r = res[k], perRound = r.net / r.rounds, sd = Math.sqrt(r.sq / r.rounds - perRound * perRound), se = sd / Math.sqrt(r.rounds);
  const seW = se * r.rounds / r.wagered;
  console.log(`  ${k.padEnd(36)} per unit wagered ${(100 * r.net / r.wagered).toFixed(3).padStart(7)}% ± ${(100 * seW).toFixed(3)} | per round ${(100 * perRound).toFixed(3).padStart(7)}% ± ${(100 * se).toFixed(3)} | avg bet ${(r.wagered / r.rounds).toFixed(2)} | SD/round ${sd.toFixed(2)}`);
  out.push({ mode, scheme: k, edge: +(100 * r.net / r.wagered).toFixed(3), edgeSe: +(100 * seW).toFixed(3), perRound: +(100 * perRound).toFixed(3), perRoundSe: +(100 * se).toFixed(3), avgBet: +(r.wagered / r.rounds).toFixed(2), sd: +sd.toFixed(2), rounds: N });
}
fs.writeFileSync(require('path').join(__dirname, `sim-${mode}.json`), JSON.stringify(out, null, 1));
