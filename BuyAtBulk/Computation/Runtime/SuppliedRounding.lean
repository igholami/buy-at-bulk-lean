import BuyAtBulk.Computation.Runtime.SuppliedMetadata
import BuyAtBulk.Computation.Runtime.SuppliedModel
import BuyAtBulk.Computation.Runtime.OriginalRoundPrepared
import BuyAtBulk.Computation.Runtime.ParameterizedPolynomial
import BuyAtBulk.Computation.Runtime.ArrayDot

/-! Full supplied-original-LP rounding. The program reads the actual weighted
path list, computes its exact metadata, rounds with arbitrary supplied integer
parameters, and projects the computed routes and purchases to the original graph. -/
set_option autoImplicit false
set_option maxHeartbeats 3600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace BuyAtBulk.Computation.Runtime.Supplied
open Rational BuyAtBulk.NodeReduction BuyAtBulk.Computation.StoredOriginal BuyAtBulk.UpperBound Original
open scoped BuyAtBulk.Computation.NodeReduction
variable {n resources h : ℕ} (tables : Tables n resources h) (fractional : Fractional tables)
variable (prepared : CachedBuffers tables) (computed : prepared=(cachedBuffers tables).value)

 def opening : Traced (Vector ℚ prepared.count) :=
   sizedPrices tables prepared.vertices prepared.count prepared.size fractional.opening 1

 def suppliedLP : NodeLP prepared.graphInput.graph h :=
   mapLP (OriginalPipeline.nodeLP tables.graphData fractional.decode) (preparedIso tables prepared computed)

 theorem opening_value (v : Fin prepared.count) :
     (opening tables fractional prepared).value[v.val]=(suppliedLP tables fractional prepared computed).opening v := by
   cases computed
   simp only [opening,sizedPrices,Weights.materialize_get,sizedPriceCell,
     resourceOpening_value,getSized_numbering tables _ (cachedBuffers tables).value.complete]
   rfl

 theorem lp_source : (suppliedLP tables fractional prepared computed).source=fun i=>prepared.source[i.val] := by
   cases computed
   exact funext fun i=>(cachedBuffers_source tables i).symm
 theorem lp_target : (suppliedLP tables fractional prepared computed).target=fun i=>prepared.target[i.val] := by
   cases computed
   exact funext fun i=>(cachedBuffers_target tables i).symm
 theorem lp_buying : (suppliedLP tables fractional prepared computed).buying=fun v=>prepared.buying[v.val] := by
   cases computed
   exact funext fun v=>(cachedBuffers_buying tables v).symm
 theorem lp_physical : (suppliedLP tables fractional prepared computed).physical=fun v=>prepared.physical[v.val] := by
   cases computed
   exact funext fun v=>(cachedBuffers_physical tables v).symm
 theorem lp_demand : (suppliedLP tables fractional prepared computed).demand=fun i=>prepared.demand[i.val] := by
   cases computed
   exact funext fun i=>(cachedBuffers_demand tables i).symm
 theorem lp_budget : (suppliedLP tables fractional prepared computed).buyingBudget=
     OriginalPipeline.buyingBudget tables.graphData fractional.decode := by
   rw [suppliedLP,mapLP_buying,OriginalPipeline.nodeLP_buying]
 theorem lp_length (i : Fin h) : (suppliedLP tables fractional prepared computed).fractionalLength i=
     OriginalPipeline.fractionalLength tables.graphData fractional.decode i := by
   rw [suppliedLP,mapLP_length,OriginalPipeline.nodeLP_length]
 theorem lp_rental : (suppliedLP tables fractional prepared computed).rentalBudget=
     OriginalPipeline.rentalBudget tables.graphData fractional.decode := by
   unfold NodeLP.rentalBudget OriginalPipeline.rentalBudget
   simp only [lp_length]
   rfl

 theorem budget_value : (ArrayDot.run tables.buying fractional.opening).value=
     OriginalPipeline.buyingBudget tables.graphData fractional.decode := by
   rw [ArrayDot.run_value]
   rfl

 def preparedRun (ratio r : ℕ) (ratio_ge : 2 ≤ ratio) : Traced (Option (StoredOriginalOutput tables)) :=
   let opens := opening tables fractional prepared
   let budget := ArrayDot.run tables.buying fractional.opening
   let lengths := metadata tables fractional.entries
   let native := StoredRounding.run prepared.graphInput prepared.buying prepared.physical opens.value budget.value
     prepared.source prepared.target lengths.value ratio r ratio_ge
   let before := opens.events++budget.events++lengths.events++native.events++[⟨.branch,[1]⟩]
   match native.value with
   | none => ⟨none,before++[⟨.write,[1]⟩]⟩
   | some output =>
     let projected := storedOutput tables prepared computed output.bought output.routes
     ⟨some projected.value,before++projected.events++[⟨.write,[1]⟩]⟩

 include computed in
 theorem native_correct (ratio r : ℕ) (ratio_ge : 8 ≤ ratio) (r_ge : 1 ≤ r) :
     ∃ output,
       (StoredRounding.run prepared.graphInput prepared.buying prepared.physical (opening tables fractional prepared).value
         (ArrayDot.run tables.buying fractional.opening).value prepared.source prepared.target
         (metadata tables fractional.entries).value ratio r (by omega)).value=some output ∧
       (nodeBuying (fun v=>prepared.buying[v.val]) (StoredState.boughtSet output.bought) : ℝ) ≤
         500000*Statements.buyingFactor h ratio r*OriginalPipeline.buyingBudget tables.graphData fractional.decode ∧
       (Rounding.rentalCost (fun v=>prepared.physical[v.val]) (fun i=>prepared.demand[i.val]) output.routes : ℝ) ≤
         500000*((r : ℝ)*Statements.gridLevels h ratio)*OriginalPipeline.rentalBudget tables.graphData fractional.decode ∧
       (output.routes.map fun e=>e.1).Perm (List.finRange h) ∧
       ∀ e∈output.routes,∀ v∈e.2.val.support,output.bought[v.val]=true := by
   obtain ⟨output,returned,buying,rental,indices,support⟩ := StoredRounding.run_correct prepared.graphInput
     (suppliedLP tables fractional prepared computed) prepared.buying prepared.physical (opening tables fractional prepared).value
     (ArrayDot.run tables.buying fractional.opening).value prepared.source prepared.target
     (metadata tables fractional.entries).value ratio r ratio_ge r_ge
     (lp_source tables fractional prepared computed) (lp_target tables fractional prepared computed)
     (lp_buying tables fractional prepared computed) (lp_physical tables fractional prepared computed)
     (funext fun v=>(opening_value tables fractional prepared computed v).symm)
     ((budget_value tables fractional).trans (lp_budget tables fractional prepared computed).symm)
     (fun i=>(metadata_value tables fractional i).trans (lp_length tables fractional prepared computed i).symm)
   rw [budget_value] at buying
   rw [lp_demand,lp_rental] at rental
   refine ⟨output,returned,buying,rental,indices,?_⟩
   intro e mem v present
   exact (StoredState.mem_boughtSet output.bought v).mp ((support e mem).1 (List.mem_toFinset.mpr present))

 def OutputSpec (ratio r : ℕ) (output : StoredOriginalOutput tables) : Prop :=
     (outputBuying tables output : ℝ) ≤ 500000*Statements.buyingFactor h ratio r*OriginalPipeline.buyingBudget tables.graphData fractional.decode ∧
     (outputRental tables output : ℝ) ≤ 500000*((r : ℝ)*Statements.gridLevels h ratio)*OriginalPipeline.rentalBudget tables.graphData fractional.decode ∧
     (output.routes.map fun e=>e.1).Perm (List.finRange h) ∧
     ∀ e∈output.routes,∀ a,OriginalPipeline.usesResource tables.graphData e.1 e.2 a=true → output.bought[a.val]=true

 theorem preparedRun_correct (ratio r : ℕ) (ratio_ge : 8 ≤ ratio) (r_ge : 1 ≤ r) :
     ∃ output,(preparedRun tables fractional prepared computed ratio r (by omega)).value=some output ∧
       OutputSpec tables fractional ratio r output := by
   obtain ⟨native,returned,buying,rental,indices,support⟩ := native_correct tables fractional prepared computed ratio r ratio_ge r_ge
   let projected := (storedOutput tables prepared computed native.bought native.routes).value
   refine ⟨projected,?_,?_,?_,?_,?_⟩
   · simp only [preparedRun,returned,projected]
   · have exactCost : outputBuying tables projected=nodeBuying (fun v=>prepared.buying[v.val]) (StoredState.boughtSet native.bought) := by
       rw [outputBuying,storedOutput_buying]
       simp only [nodeBuying,StoredState.mem_boughtSet]
     rw [exactCost];exact buying
   · have exactCost : outputRental tables projected=Rounding.rentalCost (fun v=>prepared.physical[v.val]) (fun i=>prepared.demand[i.val]) native.routes := by
       rw [outputRental,storedOutput_rental,Rounding.rentalCost_eq]
     rw [exactCost];exact rental
   · change ((storedRoutes tables prepared computed native.routes).value.map fun e=>e.1).Perm _
     rw [storedRoutes_value,List.map_map]
     exact indices
   · exact storedOutput_supported tables prepared computed native.bought native.routes support

 def run (ratio r : ℕ) (ratio_ge : 2 ≤ ratio) : Traced (Option (StoredOriginalOutput tables)) :=
   let buffers := cachedBuffers tables
   let output := preparedRun tables fractional buffers.value rfl ratio r ratio_ge
   ⟨output.value,buffers.events++output.events⟩

 theorem run_correct (ratio r : ℕ) (ratio_ge : 8 ≤ ratio) (r_ge : 1 ≤ r) :
     ∃ output,(run tables fractional ratio r (by omega)).value=some output ∧ OutputSpec tables fractional ratio r output :=
   preparedRun_correct tables fractional (cachedBuffers tables).value rfl ratio r ratio_ge r_ge

def preparedCount (n resources h m k : ℕ) := m*(50*(m+resources+1)+2)+1+10*resources+
  h*((termCount n resources+6)*k+5)+1+StoredRounding.roundingCount m h+
  resources*(27*m+9)+((14*(m+1)+17)*(m+1)+14)*h+5

theorem preparedRun_count (ratio r : ℕ) (ratio_ge : 8 ≤ ratio) (r_ge : 1 ≤ r) :
    (preparedRun tables fractional prepared computed ratio r (by omega)).events.length ≤
      preparedCount n resources h prepared.count fractional.entries.length := by
  have opens := sizedPrices_count tables prepared.vertices prepared.count prepared.size fractional.opening 1
  have dot := ArrayDot.run_count tables.buying fractional.opening
  have lengths := metadata_count tables fractional.entries
  have rounded := StoredRounding.run_count prepared.graphInput prepared.buying prepared.physical (opening tables fractional prepared).value
    (ArrayDot.run tables.buying fractional.opening).value prepared.source prepared.target
    (metadata tables fractional.entries).value ratio r (by omega)
  obtain ⟨native,returned,_,_,indices,_⟩ := native_correct tables fractional prepared computed ratio r ratio_ge r_ge
  have projected := storedOutput_count tables prepared computed native.bought native.routes
  have len : native.routes.length=h := by simpa using indices.length_eq
  rw [len] at projected
  simp only [preparedRun,returned,List.length_append,List.length_cons,List.length_nil]
  dsimp only [preparedCount,opening] at *
  omega

 def leafBudget (n resources h m k L : ℕ) := n+resources+h+m+L+
   metadataBits resources k L+2*(4*resources+1)*(L+1)+30
 def preparedWords (n resources h m k L : ℕ) :=
   leafBudget n resources h m k L+ArrayDot.wordBudget resources (L+1)+
   metadataWords n resources h k L+metadataBits resources k L+h+
   StoredRounding.roundingWords m h (leafBudget n resources h m k L)+20

 theorem cached_price_bits (values : Vector ℚ resources) (fallback : ℚ)
     (vertices : List (Vertex tables.graphData)) (m : ℕ) (size : m=vertices.length)
     (L : ℕ) (bits : ∀ a : Fin resources,(Code.ofRat values[a.val]).bits ≤ L)
     (default : (Code.ofRat fallback).bits ≤ L) (v : Fin m) :
     (Code.ofRat (sizedPrices tables vertices m size values fallback).value[v.val]).bits ≤ L := by
   simp only [sizedPrices,Weights.materialize_get,sizedPriceCell]
   exact resourceValue_output_bits tables values fallback _ L bits default

 theorem preparedRun_words (ratio r : ℕ) (ratio_ge : 2 ≤ ratio) (L : ℕ) (constant : 8 ≤ L)
     (buyingBits : ∀ a : Fin resources,(Code.ofRat tables.buying[a.val]).bits ≤ L)
     (lengthBits : ∀ a : Fin resources,(Code.ofRat tables.length[a.val]).bits ≤ L)
     (openingBits : ∀ a : Fin resources,(Code.ofRat fractional.opening[a.val]).bits ≤ L)
     (weightBits : ∀ e∈fractional.entries,(Code.ofRat e.2.1).bits ≤ L)
     (ratioBits : ratio.size ≤ L) (rBits : r.size ≤ L) :
     WordsWithin (preparedWords n resources h prepared.count fractional.entries.length L)
       (preparedRun tables fractional prepared computed ratio r ratio_ge).events := by
   let S := leafBudget n resources h prepared.count fractional.entries.length L
   let K := preparedWords n resources h prepared.count fractional.entries.length L
   have LS : L ≤ S := by dsimp[S,leafBudget];omega
   have SK : S ≤ K := by dsimp[K,preparedWords,S];omega
   have one : 1 ≤ K := by omega
   have zeroBits : (Code.ofRat 0).bits ≤ L := by norm_num [Code.ofRat,Code.bits];omega
   have oneBits : (Code.ofRat 1).bits ≤ L := by norm_num [Code.ofRat,Code.bits];omega
   have opens := (sizedPrices_words tables prepared.vertices prepared.count prepared.size fractional.opening 1 S
     (by dsimp[S,leafBudget];omega) (fun a=>(openingBits a).trans LS) (oneBits.trans LS)).mono SK
   have dot := (ArrayDot.run_words tables.buying fractional.opening (L+1) (by omega)
     (fun a=>by have := buyingBits a;omega) (fun a=>by have := openingBits a;omega)).mono
     (show _ ≤ K by dsimp[K,preparedWords];omega)
   have lengths := (metadata_words tables fractional.entries L (by omega) lengthBits weightBits).mono
     (show _ ≤ K by dsimp[K,preparedWords];omega)
   have budgetBits := ArrayDot.run_bits tables.buying fractional.opening (L+1) (by omega)
     (fun a=>by have := buyingBits a;omega) (fun a=>by have := openingBits a;omega)
   have bBits (v : Fin prepared.count) : (Code.ofRat prepared.buying[v.val]).bits ≤ S := by
     cases computed
     exact (cached_price_bits tables tables.buying 0 _ _ _ L buyingBits zeroBits v).trans LS
   have pBits (v : Fin prepared.count) : (Code.ofRat prepared.physical[v.val]).bits ≤ S := by
     cases computed
     exact (cached_price_bits tables tables.length 0 _ _ _ L lengthBits zeroBits v).trans LS
   have oBits (v : Fin prepared.count) : (Code.ofRat (opening tables fractional prepared).value[v.val]).bits ≤ S :=
     (cached_price_bits tables fractional.opening 1 _ _ _ L openingBits oneBits v).trans LS
   have lBits (i : Fin h) : (Code.ofRat (metadata tables fractional.entries).value[i.val]).bits ≤ S := by
     rw [metadata,Weights.materialize_get]
     exact (commodity_bits tables i fractional.entries L (by omega) lengthBits weightBits).trans (by dsimp[S,leafBudget];omega)
   have rounded := (StoredRounding.run_words prepared.graphInput prepared.buying prepared.physical (opening tables fractional prepared).value
     (ArrayDot.run tables.buying fractional.opening).value prepared.source prepared.target
     (metadata tables fractional.entries).value ratio r ratio_ge S (by omega) bBits pBits oBits
     (budgetBits.trans (by dsimp[S,leafBudget];omega)) lBits (ratioBits.trans LS) (rBits.trans LS)).mono
     (show _ ≤ K by dsimp[K,preparedWords,S];omega)
   change WordsWithin K _
   unfold preparedRun
   dsimp only
   split
   · simp_all [wordsWithin_append,wordsWithin_cons,opening]
   · rename_i output returned
     have projected := storedOutput_words tables prepared computed output.bought output.routes K
       (by dsimp[K,preparedWords,leafBudget];omega)
     simp_all [wordsWithin_append,wordsWithin_cons,opening]

 def countBudget (n resources h k : ℕ) :=
   cachedCount n resources h (n+n*n+2*h)+preparedCount n resources h (n+n*n+2*h) k
 def wordBudget (n resources h k L : ℕ) :=
   cachedWordBudget n resources h L+preparedWords n resources h (n+n*n+2*h) k L

 theorem run_count (ratio r : ℕ) (ratio_ge : 8 ≤ ratio) (r_ge : 1 ≤ r) :
     (run tables fractional ratio r (by omega)).events.length ≤ countBudget n resources h fractional.entries.length := by
   have cached := cachedBuffers_count_polynomial tables
   have rounded := preparedRun_count tables fractional (cachedBuffers tables).value rfl ratio r ratio_ge r_ge
   have dimension := cachedBuffers_dimension tables
   have roundedMono : StoredRounding.roundingCount (cachedBuffers tables).value.count h ≤
       StoredRounding.roundingCount (n+n*n+2*h) h := by
     rw [←RoundingPolynomial.roundingCount_eval,←RoundingPolynomial.roundingCount_eval]
     apply PolynomialBudget.Term.eval_mono
     intro i
     simp only[RoundingPolynomial.two]
     split_ifs <;>omega
   have monotone : preparedCount n resources h (cachedBuffers tables).value.count fractional.entries.length ≤
       preparedCount n resources h (n+n*n+2*h) fractional.entries.length := by
     dsimp only [preparedCount]
     gcongr
   simp only [run,List.length_append]
   exact (Nat.add_le_add cached (rounded.trans monotone))

 theorem run_words (ratio r : ℕ) (ratio_ge : 2 ≤ ratio) (L : ℕ) (constant : 8 ≤ L)
     (buyingBits : ∀ a : Fin resources,(Code.ofRat tables.buying[a.val]).bits ≤ L)
     (lengthBits : ∀ a : Fin resources,(Code.ofRat tables.length[a.val]).bits ≤ L)
     (demandBits : ∀ i : Fin h,(Code.ofRat tables.demand[i.val]).bits ≤ L)
     (openingBits : ∀ a : Fin resources,(Code.ofRat fractional.opening[a.val]).bits ≤ L)
     (weightBits : ∀ e∈fractional.entries,(Code.ofRat e.2.1).bits ≤ L)
     (ratioBits : ratio.size ≤ L) (rBits : r.size ≤ L) :
     WordsWithin (wordBudget n resources h fractional.entries.length L)
       (run tables fractional ratio r ratio_ge).events := by
   have dimension := cachedBuffers_dimension tables
   have leafMono : leafBudget n resources h (cachedBuffers tables).value.count fractional.entries.length L ≤
       leafBudget n resources h (n+n*n+2*h) fractional.entries.length L := by
     dsimp only[leafBudget]
     omega
   have roundedMono : StoredRounding.roundingWords (cachedBuffers tables).value.count h
       (leafBudget n resources h (cachedBuffers tables).value.count fractional.entries.length L) ≤
       StoredRounding.roundingWords (n+n*n+2*h) h
         (leafBudget n resources h (n+n*n+2*h) fractional.entries.length L) := by
     rw [←RoundingPolynomial.roundingWords_eval,←RoundingPolynomial.roundingWords_eval]
     apply PolynomialBudget.Term.eval_mono
     intro i
     simp only[RoundingPolynomial.three]
     split_ifs <;>omega
   have monotone : preparedWords n resources h (cachedBuffers tables).value.count fractional.entries.length L ≤
       preparedWords n resources h (n+n*n+2*h) fractional.entries.length L := by
     dsimp only[preparedWords]
     omega
   have cached := (cachedBuffers_words_polynomial tables L buyingBits lengthBits demandBits).mono
     (show _ ≤ wordBudget n resources h fractional.entries.length L by dsimp[wordBudget];omega)
   have rounded := (preparedRun_words tables fractional (cachedBuffers tables).value rfl ratio r ratio_ge L constant
     buyingBits lengthBits openingBits weightBits ratioBits rBits).mono
     (monotone.trans (show _ ≤ wordBudget n resources h fractional.entries.length L by dsimp[wordBudget];omega))
   exact (wordsWithin_append _ _ _).mpr ⟨cached,rounded⟩

end BuyAtBulk.Computation.Runtime.Supplied
