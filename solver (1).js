/**
 * solver.js — Quine-McCluskey K-Map Minimization Engine
 * Supports 3, 4, 5, 6 variables
 */

const VAR_NAMES_ALL = ['A', 'B', 'C', 'D', 'E', 'F'];
const GROUP_COLORS = [
  '#ff6584', '#6c63ff', '#43e97b', '#ffd166',
  '#ef476f', '#06d6a0', '#118ab2', '#ff9f1c'
];

/* ─── State ─────────────────────────────────────────── */
let numVars    = 4;
let minterms   = new Set();
let dontcares  = new Set();
let inputMode  = 'minterm'; // 'minterm' | 'dontcare'

/* ─── Helpers ────────────────────────────────────────── */
function getVarNames()  { return VAR_NAMES_ALL.slice(0, numVars); }
function getMaxTerms()  { return 1 << numVars; }

function countBits(n) {
  let c = 0;
  while (n) { c += n & 1; n >>>= 1; }
  return c;
}

/* ─── K-Map layout per variable count ───────────────── */
function getKMapLayout() {
  switch (numVars) {
    case 3: return {
      rowBits: 1, colBits: 2,
      rowOrder: [0, 1],
      colOrder: [0, 1, 3, 2],
      rowLabels: ['0', '1'],
      colLabels: ['00', '01', '11', '10'],
      rowVars: 'A', colVars: 'BC'
    };
    case 4: return {
      rowBits: 2, colBits: 2,
      rowOrder: [0, 1, 3, 2],
      colOrder: [0, 1, 3, 2],
      rowLabels: ['00', '01', '11', '10'],
      colLabels: ['00', '01', '11', '10'],
      rowVars: 'AB', colVars: 'CD'
    };
    case 5: return {
      rowBits: 2, colBits: 3,
      rowOrder: [0, 1, 3, 2],
      colOrder: [0, 1, 3, 2, 6, 7, 5, 4],
      rowLabels: ['00', '01', '11', '10'],
      colLabels: ['000','001','011','010','110','111','101','100'],
      rowVars: 'AB', colVars: 'CDE'
    };
    case 6: return {
      rowBits: 3, colBits: 3,
      rowOrder: [0, 1, 3, 2, 6, 7, 5, 4],
      colOrder: [0, 1, 3, 2, 6, 7, 5, 4],
      rowLabels: ['000','001','011','010','110','111','101','100'],
      colLabels: ['000','001','011','010','110','111','101','100'],
      rowVars: 'ABC', colVars: 'DEF'
    };
  }
}

function cellIndex(r, c) {
  const l = getKMapLayout();
  return (l.rowOrder[r] << l.colBits) | l.colOrder[c];
}

/* ─── Quine-McCluskey ────────────────────────────────── */
function quine() {
  const N          = numVars;
  const allM       = [...minterms];
  const allDC      = [...dontcares];
  const workSet    = new Set([...allM, ...allDC]);
  const iterations = [];

  if (workSet.size === 0)     return { pis:[], epis:[], expr:'0', iterations, piToTerm };
  if (allM.length === getMaxTerms()) return { pis:[], epis:[], expr:'1', iterations, piToTerm };

  /* Initial grouping by number of 1-bits */
  let groups = new Map();
  for (const m of workSet) {
    const bc = countBits(m);
    if (!groups.has(bc)) groups.set(bc, []);
    groups.get(bc).push({ terms: [m], mask: 0, used: false, isDC: !minterms.has(m) });
  }

  const snap = (g) => {
    const out = [];
    [...g.keys()].sort((a,b)=>a-b).forEach(k => out.push(...g.get(k).map(t=>({...t,terms:[...t.terms]}))));
    return out;
  };
  iterations.push({ round: 1, terms: snap(groups) });

  let primeImplicants = [];

  for (let round = 0; round < N; round++) {
    const newGroups = new Map();
    const seen      = new Set();
    const sortedKeys = [...groups.keys()].sort((a,b)=>a-b);

    for (let i = 0; i < sortedKeys.length - 1; i++) {
      const g1 = groups.get(sortedKeys[i])   || [];
      const g2 = groups.get(sortedKeys[i+1]) || [];

      for (const t1 of g1) {
        for (const t2 of g2) {
          if (t1.mask !== t2.mask) continue;
          const rep1 = t1.terms[0], rep2 = t2.terms[0];
          const diff = (rep1 ^ rep2) & ~t1.mask;
          if (!diff || (diff & (diff - 1))) continue;   // not exactly 1 bit differs

          t1.used = true;
          t2.used = true;

          const newMask  = t1.mask | diff;
          const combined = [...new Set([...t1.terms, ...t2.terms])].sort((a,b)=>a-b);
          const key      = combined.join(',') + '_' + newMask;
          if (seen.has(key)) continue;
          seen.add(key);

          const bc    = countBits(combined[0] & ~newMask);
          const isDC  = combined.every(t => !minterms.has(t));
          if (!newGroups.has(bc)) newGroups.set(bc, []);
          newGroups.get(bc).push({ terms: combined, mask: newMask, used: false, isDC });
        }
      }
    }

    /* Collect unused → prime implicants */
    for (const [, grp] of groups)
      for (const t of grp)
        if (!t.used && !t.isDC) primeImplicants.push({ ...t, terms: [...t.terms] });

    if (newGroups.size === 0) break;
    groups = newGroups;
    iterations.push({ round: round + 2, terms: snap(groups) });
  }
  /* Remaining last round */
  for (const [, grp] of groups)
    for (const t of grp)
      if (!t.isDC) primeImplicants.push({ ...t, terms: [...t.terms] });

  /* De-duplicate */
  const dedupMap = new Map();
  for (const pi of primeImplicants) {
    const key = pi.terms.join(',') + '_' + pi.mask;
    if (!dedupMap.has(key)) dedupMap.set(key, pi);
  }
  primeImplicants = [...dedupMap.values()];

  /* Essential PI selection */
  const epis    = [];
  const covered = new Set();

  for (const m of allM) {
    const covering = primeImplicants.filter(pi => pi.terms.includes(m));
    if (covering.length === 1) {
      const epi = covering[0];
      if (!epis.includes(epi)) {
        epis.push(epi);
        epi.terms.filter(t => minterms.has(t)).forEach(t => covered.add(t));
      }
    }
  }

  /* Greedy cover for remaining */
  let remaining = allM.filter(m => !covered.has(m));
  const nonEPI  = primeImplicants.filter(pi => !epis.includes(pi));

  while (remaining.length > 0) {
    let best = null, bestCount = 0;
    for (const pi of nonEPI) {
      const c = pi.terms.filter(t => remaining.includes(t)).length;
      if (c > bestCount) { bestCount = c; best = pi; }
    }
    if (!best) break;
    epis.push(best);
    remaining = remaining.filter(m => !best.terms.includes(m));
  }

  /* Build expression */
  const exprTerms = epis.map(pi => piToTerm(pi));
  const expr = exprTerms.length === 0 ? '0' : exprTerms.join(' + ');

  return { pis: primeImplicants, epis, expr, iterations, piToTerm };
}

function piToTerm(pi) {
  const vars = getVarNames();
  const N    = numVars;
  let term   = '';
  for (let i = 0; i < N; i++) {
    const bit = N - 1 - i;
    if (!(pi.mask & (1 << bit))) {
      const val = (pi.terms[0] >> bit) & 1;
      term += val === 0 ? vars[i] + "'" : vars[i];
    }
  }
  return term || '1';
}

/* ─── Public API ─────────────────────────────────────── */
window.KMapSolver = {
  /* getters */
  getNumVars:    () => numVars,
  getMinterms:   () => minterms,
  getDontcares:  () => dontcares,
  getInputMode:  () => inputMode,
  getVarNames,
  getMaxTerms,
  getKMapLayout,
  cellIndex,
  countBits,
  piToTerm,
  GROUP_COLORS,

  /* setters */
  setNumVars(n) {
    numVars   = n;
    minterms  = new Set();
    dontcares = new Set();
  },
  setInputMode(m) { inputMode = m; },

  toggleCell(idx) {
    if (minterms.has(idx)) {
      minterms.delete(idx);
      if (inputMode === 'dontcare') dontcares.add(idx);
    } else if (dontcares.has(idx)) {
      dontcares.delete(idx);
    } else {
      if (inputMode === 'minterm') minterms.add(idx);
      else dontcares.add(idx);
    }
  },

  clearAll() { minterms = new Set(); dontcares = new Set(); },

  solve: quine
};
