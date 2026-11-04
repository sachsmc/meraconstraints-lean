// Generate exact integer witnesses; every exported statement is checked by Lean.
// Run: node scripts/generate-iv-facets.mjs
import { readFileSync, writeFileSync } from 'node:fs';
const source=readFileSync(new URL('../MeraConstraints/Examples/InstrumentalAppendix.lean',import.meta.url),'utf8');
function matrix(name) {
  const match=source.match(new RegExp('def '+name+'\\b[^\\n]*:=\\s*!!\\[([\\s\\S]*?)\\]'));
  if(!match)throw Error('Missing '+name);
  return match[1].split(';').map(row=>row.match(/-?\d+/g).map(Number));
}
const B=matrix('printedB'), H=matrix('printedHi');
const upper=source.match(/def printedUpper\b[^\n]*:=\s*!\[([^\]]*)\]/)[1].match(/-?\d+/g).map(Number);
function rank(A) {
  A=A.map(r=>[...r]); let k=0;
  for(let c=0;c<A[0].length && k<A.length;c++) {
    let p=A.findIndex((r,i)=>i>=k && r[c]!==0); if(p<0)continue;
    [A[k],A[p]]=[A[p],A[k]]; const d=A[k][c]; A[k]=A[k].map(x=>x/d);
    for(let i=0;i<A.length;i++)if(i!==k){const t=A[i][c];A[i]=A[i].map((x,j)=>x-t*A[k][j]);}
    k++;
  }
  return k;
}
function inverse(A) {
  const n=A.length, M=A.map((r,i)=>[...r,...Array.from({length:n},(_,j)=>i===j?1:0)]);
  for(let c=0;c<n;c++) {
    const p=M.findIndex((r,i)=>i>=c && r[c]!==0); if(p<0)throw Error('Singular minor');
    [M[c],M[p]]=[M[p],M[c]]; const d=M[c][c]; M[c]=M[c].map(x=>x/d);
    for(let i=0;i<n;i++)if(i!==c){const t=M[i][c];M[i]=M[i].map((x,j)=>x-t*M[c][j]);}
  }
  return M.map(r=>r.slice(n));
}
function combinations(xs,n) {
  if(n===0)return [[]]; if(xs.length<n)return [];
  return [...combinations(xs.slice(1),n-1).map(s=>[xs[0],...s]),...combinations(xs.slice(1),n)];
}
const slack=(f,j)=>upper[f]-H[f].reduce((s,h,i)=>s+h*B[i][j],0);
const selected=[],readers=[],proper=[];
for(let f=0;f<12;f++) {
  const tight=Array.from({length:16},(_,j)=>j).filter(j=>slack(f,j)===0);
  const cols=[];
  for(const j of tight)if(rank(B.map(row=>[...cols,j].map(c=>row[c])))>cols.length)cols.push(j);
  if(cols.length!==6)throw Error('Expected rank six on facet '+f);
  selected.push(cols);
  const rows=combinations([0,1,2,3,4,5,6,7],6).find(rs=>rank(rs.map(i=>cols.map(j=>B[i][j])))===6);
  const inv=inverse(rows.map(i=>cols.map(j=>B[i][j])));
  if(inv.flat().some(x=>!Number.isInteger(x)))throw Error('Expected integral left inverse');
  readers.push(inv.map(row=>Array.from({length:8},(_,i)=>rows.includes(i)?row[rows.indexOf(i)]:0)));
  proper.push(Array.from({length:16},(_,j)=>j).find(j=>slack(f,j)>0));
}
const separating=Array.from({length:12},(_,f)=>Array.from({length:12},(_,g)=>{
  if(f===g)return 0;
  const j=Array.from({length:16},(_,j)=>j).find(j=>slack(f,j)===0 && slack(g,j)>0);
  if(j===undefined)throw Error('No separating witness');
  return j;
}));
const mat=rows=>'!!['+rows.map(r=>r.join(',')).join(';\n     ')+']';
const vec=xs=>'!['+xs.join(',')+']';
const lines=[
'import MeraConstraints.Examples.InstrumentalHull',
'',
'/-!',
'# Exact integer witnesses for the twelve Appendix B facets',
'',
'For each printed H inequality we select six incident response columns and',
'an integer left inverse of their eight-by-six column matrix. Tightness,',
'strict off-plane columns and pairwise separation are finite integer checks.',
'The casts to the literal real B and H data are proved entry by entry.',
'The generator scripts/generate-iv-facets.mjs is not trusted: its complete',
'output is checked by Lean. Facet dimension arguments are in InstrumentalFacets.',
'-/',
'',
'namespace MeraConstraints.Examples.Instrumental.Appendix',
'',
'def facetIntegerB : Matrix (Fin 8) (Fin 16) ℤ :=\n  '+mat(B),
'',
'def facetIntegerHi : Matrix (Fin 12) (Fin 8) ℤ :=\n  '+mat(H),
'',
'def facetIntegerUpper : Fin 12 → ℤ := '+vec(upper),
'',
'/-- Six zero-based printed response-column indices for each H row. -/',
'def facetColumn : Fin 12 → Fin 6 → Fin 16 :=\n  !['+selected.map(vec).join(',\n    ')+']',
'',
'def facetReader : Fin 12 → Matrix (Fin 6) (Fin 8) ℤ :=\n  !['+readers.map(mat).join(',\n    ')+']',
'',
'def facetProperColumn : Fin 12 → Fin 16 := '+vec(proper),
'',
'def facetSeparatingColumn : Matrix (Fin 12) (Fin 12) (Fin 16) :=\n  '+mat(separating),
'',
'def facetIntegerSlack (f : Fin 12) (j : Fin 16) : ℤ :=',
'  facetIntegerUpper f - ∑ i, facetIntegerHi f i * facetIntegerB i j',
'',
'set_option maxHeartbeats 2000000 in',
'theorem facetIntegerB_cast (i : Fin 8) (j : Fin 16) :',
'    (facetIntegerB i j : ℝ) = printedB i j := by',
'  fin_cases i <;> fin_cases j <;> norm_num [facetIntegerB, printedB]',
'',
'set_option maxHeartbeats 2000000 in',
'theorem facetIntegerHi_cast (f : Fin 12) (i : Fin 8) :',
'    (facetIntegerHi f i : ℝ) = printedHi f i := by',
'  fin_cases f <;> fin_cases i <;> norm_num [facetIntegerHi, printedHi]',
'',
'theorem facetIntegerUpper_cast (f : Fin 12) : (facetIntegerUpper f : ℝ) = printedUpper f := by',
'  fin_cases f <;> norm_num [facetIntegerUpper, printedUpper]',
'',
'theorem facetIntegerSlack_cast (f : Fin 12) (j : Fin 16) :',
'    (facetIntegerSlack f j : ℝ) = Geometry.slack (printedHi f) (printedUpper f) (fun i => printedB i j) := by',
'  unfold facetIntegerSlack Geometry.slack',
'  push_cast',
'  simp only [facetIntegerUpper_cast, facetIntegerHi_cast, facetIntegerB_cast]',
'',
'set_option maxRecDepth 4096 in',
'set_option maxHeartbeats 4000000 in',
'theorem facet_reader_integer_identity : ∀ (f : Fin 12) (i j : Fin 6),',
'    (∑ k, facetReader f i k * facetIntegerB k (facetColumn f j)) = if i = j then 1 else 0 := by',
'  decide',
'',
'set_option maxRecDepth 4096 in',
'set_option maxHeartbeats 4000000 in',
'theorem facet_selected_integer_tight : ∀ (f : Fin 12) (j : Fin 6),',
'    facetIntegerSlack f (facetColumn f j) = 0 := by decide',
'',
'set_option maxRecDepth 4096 in',
'set_option maxHeartbeats 4000000 in',
'theorem facet_proper_integer_positive : ∀ f : Fin 12,',
'    0 < facetIntegerSlack f (facetProperColumn f) := by decide',
'',
'set_option maxRecDepth 4096 in',
'set_option maxHeartbeats 4000000 in',
'theorem facet_separation_integer : ∀ f g : Fin 12, f ≠ g →',
'    facetIntegerSlack f (facetSeparatingColumn f g) = 0 ∧',
'      0 < facetIntegerSlack g (facetSeparatingColumn f g) := by decide',
'',
'noncomputable def facetColumnMatrix (f : Fin 12) : Matrix (Fin 8) (Fin 6) ℝ :=',
'  fun i j => printedB i (facetColumn f j)',
'',
'noncomputable def facetReaderMatrix (f : Fin 12) : Matrix (Fin 6) (Fin 8) ℝ :=',
'  fun j i => (facetReader f j i : ℝ)',
'',
'theorem facet_reader_mul_columns (f : Fin 12) :',
'    facetReaderMatrix f * facetColumnMatrix f = 1 := by',
'  ext i j',
'  simp only [Matrix.mul_apply, Matrix.one_apply, facetReaderMatrix, facetColumnMatrix]',
'  simp_rw [← facetIntegerB_cast]',
'  exact_mod_cast facet_reader_integer_identity f i j',
'',
'end MeraConstraints.Examples.Instrumental.Appendix',
''];
writeFileSync(new URL('../MeraConstraints/Examples/InstrumentalFacetData.lean',import.meta.url),lines.join('\n'));
console.log('Generated twelve rank-six integer left inverses, incident and separation witnesses.');
