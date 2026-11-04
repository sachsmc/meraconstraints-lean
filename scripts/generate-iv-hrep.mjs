// Generates a symbolic bound certificate; Lean checks every arithmetic step.
// Run: node scripts/generate-iv-hrep.mjs
import { writeFileSync } from 'node:fs';

const size = 13; // five free weights followed by eight probability coordinates
const vector = terms => {
  const v = Array(size).fill(0);
  for (const [i, c] of terms) v[i] = c;
  return v;
};
// Solve the margin equations, retaining columns 0,1,3,4,5,6,8,9,11,12,13,14.
// The free weights t0,...,t4 are columns 0,1,4,5,8.
const original = [
  ...[0,1,2,3,4].map(i => vector([[i,1]])),
  vector([[5,1],[0,-1],[1,-1]]),
  vector([[6,1],[2,-1],[3,-1]]),
  vector([[10,1],[1,-1],[3,-1]]),
  vector([[7,1],[10,-1],[1,1],[3,1],[4,-1]]),
  vector([[9,1],[0,-1],[2,-1]]),
  vector([[11,1],[6,-1],[2,1],[3,1],[4,-1]]),
  vector([[8,1],[9,-1],[11,-1],[6,1],[0,1],[3,-1],[4,1]])
];
function gcd(a,b) { while (b) [a,b] = [b,a%b]; return Math.abs(a); }
function normalize(v) {
  const g = v.reduce((a,b) => gcd(a,b), 0);
  return g ? v.map(x => x/g) : v;
}
const key = v => normalize(v).join(',');
function eliminate(cs,k) {
  const lower = cs.filter(c => c[k]>0), upper = cs.filter(c => c[k]<0);
  const all = [
    ...cs.filter(c => c[k]===0),
    ...lower.flatMap(a => upper.map(b => a.map((v,i) => -b[k]*v+a[k]*b[i])))
  ];
  const unique = new Map();
  for (const raw of all) {
    const v = normalize(raw);
    if (v.some(x => x)) unique.set(v.join(','), v);
  }
  return [...unique.values()];
}
const stages = [];
let current = original;
for (let k=0; k<5; k++) {
  const next = eliminate(current,k);
  stages.push({k,before:current,after:next});
  current = next;
}
function expression(v) {
  let result = '';
  v.forEach((c,i) => {
    if (!c) return;
    const atom = i<5 ? 't'+i : 'p '+(i-5);
    const term = Math.abs(c)===1 ? atom : Math.abs(c)+' * '+atom;
    result += result ? (c>0 ? ' + ' : ' - ')+term : (c>0 ? '' : '-')+term;
  });
  return result || '0';
}
function bound(c,k) {
  const rest = [...c]; rest[k] = 0;
  const e = expression(rest), a = Math.abs(c[k]);
  const numerator = c[k]>0 ? '-('+e+')' : '('+e+')';
  return a===1 ? numerator : '('+numerator+') / '+a;
}
function maximum(ls) {
  return ls.length===1 ? ls[0] : 'max ('+ls[0]+') ('+maximum(ls.slice(1))+')';
}
function lowerProof(ls,i) {
  if (ls.length===1) return 'le_rfl';
  if (i===0) return 'le_max_left _ _';
  return 'le_trans ('+lowerProof(ls.slice(1),i-1)+') (le_max_right _ _)';
}
const code = [
'import MeraConstraints.Examples.InstrumentalAppendix',
'',
'/-!',
'# Exact Appendix B IV H-representation',
'',
'Every feasible printed H vector is reconstructed as a simplex mixture of',
'the printed response columns. Seven independent margin equations express',
'twelve distinct-column weights in terms of five free weights t0,...,t4.',
'The other four profile weights are zero. All twelve retained weights must',
'be nonnegative.',
'',
'The finite Fourier–Motzkin certificate below eliminates the free weights',
'in order and reconstructs them in reverse order as maxima of lower bounds.',
'Every lower/upper comparison is checked by linear arithmetic in Lean.',
'The final inequalities follow from the literal twelve H inequalities and',
'two normalizations. No strict positivity, division by a probability, or',
'external solver is used; boundary points are included.',
'',
'The certificate is generated reproducibly by scripts/generate-iv-hrep.mjs.',
'The generator is outside the proof kernel: all its output is an explicit',
'Lean proof. The resulting HRep has exactly the manuscript matrices.',
'-/',
'',
'namespace MeraConstraints.Examples.Instrumental.Appendix',
'',
'set_option maxHeartbeats 4000000 in',
'/-- Reverse H inclusion, with explicit nonnegative response-profile weights. -/',
'theorem printed_feasible_mixture {p : Fin 8 → ℝ} (hp : PrintedFeasible p) :',
'    p ∈ Polytope.mixture printedB := by',
'  have hpvec : p = ![p 0, p 1, p 2, p 3, p 4, p 5, p 6, p 7] := by',
'    funext i',
'    fin_cases i <;> rfl'
];
for(let i=0;i<12;i++) code.push('  have hi'+i+' := hp.1 ('+i+' : Fin 12)');
for(let i=0;i<2;i++) code.push('  have he'+i+' := hp.2 ('+i+' : Fin 2)');
const seeds=[...Array.from({length:12},(_,i)=>'hi'+i),'he0','he1'];
// Each change is checked definitionally against the original printed matrix.
const hi = [
  [0,0,0,0,-1,0,0,0],[-1,-1,-1,0,0,1,0,0],[0,1,0,0,-1,-1,-1,0],
  [-1,0,0,0,0,0,0,0],[0,0,1,0,1,0,0,0],[1,0,0,0,0,0,1,0],
  [0,0,0,0,0,-1,0,0],[0,0,0,0,1,1,1,0],[0,-1,0,0,0,0,0,0],
  [1,1,1,0,0,0,0,0],[0,0,0,0,0,0,-1,0],[0,0,-1,0,0,0,0,0]
];
const upper = [0,0,0,0,1,1,0,1,0,1,0,0];
hi.forEach((row,i)=>code.push('  change (∑ i : Fin 8, !['+row.join(',')+'] i * p i) ≤ '+upper[i]+' at hi'+i));
code.push('  change (∑ i : Fin 8, ![-1,-1,-1,-1,0,0,0,0] i * p i) = -1 at he0');
code.push('  change (∑ i : Fin 8, ![0,0,0,0,-1,-1,-1,-1] i * p i) = -1 at he1');
code.push('  rw [hpvec] at '+seeds.join(' '));
code.push('  norm_num [Fin.sum_univ_succ] at '+seeds.join(' '));
code.push('  -- Fully eliminated inequalities: consequences of the printed H rows.');
current.forEach((v,i)=>code.push('  have h5_'+i+' : 0 ≤ '+expression(v)+' := by linarith only ['+seeds.join(', ')+']'));
for(let s=4;s>=0;s--) {
  const {k,before,after}=stages[s], positives=before.filter(c=>c[k]>0), negatives=before.filter(c=>c[k]<0);
  const ls=positives.map(c=>bound(c,k));
  code.push('  -- Reconstruct free column weight t'+k+' from its interval of feasible values.');
  code.push('  let t'+k+' : ℝ := '+maximum(ls));
  ls.forEach((l,i)=>code.push('  have l'+k+'_'+i+' : ('+l+') ≤ t'+k+' := '+lowerProof(ls,i)));
  negatives.forEach((u,j)=>{
    function leaf(l) {
      const c=l.map((v,i)=>-u[k]*v+l[k]*u[i]);
      const index=after.findIndex(a=>key(a)===key(c));
      if (index<0 && c.some(x=>x)) throw Error('Missing elimination certificate');
      return '(by linarith only ['+(index<0?'':'h'+(s+1)+'_'+index)+'])';
    }
    function upperProof(ps) {
      return ps.length===1 ? leaf(ps[0]) : '(max_le '+leaf(ps[0])+' '+upperProof(ps.slice(1))+')';
    }
    code.push('  have u'+k+'_'+j+' : t'+k+' ≤ ('+bound(u,k)+') := by');
    code.push('    dsimp only [t'+k+']');
    code.push('    exact '+upperProof(positives));
  });
  before.forEach((c,i)=>{
    let source;
    if(c[k]>0) source='l'+k+'_'+positives.indexOf(c);
    else if(c[k]<0) source='u'+k+'_'+negatives.indexOf(c);
    else {
      const j=after.findIndex(a=>key(a)===key(c));
      if(j<0)throw Error('Missing preserved inequality');
      source='h'+(s+1)+'_'+j;
    }
    code.push('  have h'+s+'_'+i+' : 0 ≤ '+expression(c)+' := by linarith only ['+source+']');
  });
}
code.push(
'  -- Four duplicate-column profiles receive zero; all margins are preserved.',
'  let q : Fin 16 → ℝ :=',
'    ![t0, t1, 0, p 0 - t0 - t1, t2, t3, p 1 - t2 - t3, 0,',
'      t4, p 5 - t1 - t3, 0, p 2 - p 5 + t1 + t3 - t4,',
'      p 4 - t0 - t2, p 3 - p 4 - p 6 + p 1 + t0 - t3 + t4,',
'      p 6 - p 1 + t2 + t3 - t4, 0]',
'  refine ⟨q, ⟨?_, ?_⟩, ?_⟩',
'  · intro j',
'    fin_cases j <;> norm_num [q] <;>',
'      linarith only ['+original.map((_,i)=>'h0_'+i).join(', ')+']',
'  · norm_num [q, Fin.sum_univ_succ]',
'    linarith only [he0]',
'  · funext i',
'    conv_rhs => rw [hpvec]',
'    fin_cases i <;>',
'      norm_num [Matrix.mulVec, dotProduct, printedB, q, Fin.sum_univ_succ] <;>',
'      linarith only [he0, he1]',
'',
'theorem printed_mixture_iff_feasible (p : Fin 8 → ℝ) :',
'    p ∈ Polytope.mixture printedB ↔ PrintedFeasible p :=',
'  ⟨printed_mixture_feasible, printed_feasible_mixture⟩',
'',
'/-- Literal Appendix B H data, now with kernel-checked V-to-H exactness. -/',
'noncomputable def printedHRep : Polytope.HRep printedB (Fin 12) (Fin 2) where',
'  inequalities := printedHi',
'  upper := printedUpper',
'  equalities := printedHe',
'  target := printedTarget',
'  exact_representation := printed_mixture_iff_feasible',
'',
'end MeraConstraints.Examples.Instrumental.Appendix',
'');
writeFileSync(new URL('../MeraConstraints/Examples/InstrumentalHRep.lean',import.meta.url),code.join('\n'));
console.log('Generated InstrumentalHRep.lean; '+current.length+' terminal bounds, five reconstructed weights.');
