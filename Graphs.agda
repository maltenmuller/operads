module Graphs where

open import Level using (Level) renaming (zero to 0l)
open import Agda.Builtin.Equality
open import Relation.Binary.PropositionalEquality

open import Data.Nat  renaming (_+_  to _+N_; _≤_ to _<=N_)
open import Data.Nat.Properties
open import Data.List renaming (_++_ to _+L_; map to mapL; replicate to replicateL; lookup to lookupL) hiding ([_])
open import Data.Vec  renaming (_++_ to _+V_; map to mapV) hiding ([_])
open import Data.Fin
open import Data.Product

--open import Categories.Category.Monoidal
open import Categories.Category


--------------------------------------------------------------------------------
--  Graphs represented by Rotation Systems
--------------------------------------------------------------------------------

-- type of graphs

data Edge : Set where
  e : Edge

data Graph : ℕ → ℕ → {ℕ} → Set where
  gr : (ls : List Edge)
    → {v : ℕ} → Vec (List (Fin (length ls))) v
    → {i o : ℕ} → Vec (Fin (length ls)) i × Vec (Fin (length ls)) o
    → Graph i o {v}
{-data Graph (i o : ℕ){v : ℕ} : Set where
  gr : (ls : List Edge)
     → Vec (List (Fin (length ls))) v
     → Vec (Fin (length ls)) i × Vec (Fin (length ls)) o
     → Graph i o
-}
emptyGraph : Graph 0 0
emptyGraph = gr []  []  ([] , [])

id1 : Graph 1 1
id1 = gr (e ∷ []) [] (0F ∷ [] , 0F ∷ [])

cup : Graph 2 0
cup = gr (e ∷ []) [] (0F ∷ 0F ∷ [] , [])

cap : Graph 0 2
cap = gr (e ∷ []) [] ([] , 0F ∷ 0F ∷ [])

--------------------------
-- parallel composition
--------------------------

-- opposite of raise : ∀ {m} n → Fin m → Fin (n ℕ.+ m)
extend : ∀ {n} m → Fin n → Fin (n +N m)
extend {n} m f = inject≤ f (helper n m )
  where
    helper : (n m : ℕ) -> n <=N (n +N m)
    helper 0 m = z≤n
    helper (suc n) m  = s≤s (helper n m)

lengthFun : {X : Set}(ls ls' : List X) → length ls +N length ls' ≡ length (ls +L ls')
lengthFun [] ls' = refl
lengthFun (x ∷ ls) ls' = cong suc (lengthFun ls ls')


parallel : {i o i' o' v v' : ℕ} → Graph i o {v} → Graph i' o' {v'} → Graph (i +N i') (o +N o') {v +N v'}
parallel {i}{o}{i'}{o'}{v = v}{v'} (gr es vs (is , os)) (gr es' vs' (is' , os'))
  = gr (es +L es') ((vsExt' +V vs'Rai')) (isExt +V is'Rai , osExt +V os'Rai) where

    vsExt = mapV (\ l → mapL (extend (length es')) l) vs
    vsExt' = subst (\ a → Vec (List (Fin a)) v) (lengthFun es es') vsExt
    vs'Rai = mapV (\ l → mapL (raise (length es)) l) vs'
    vs'Rai' = subst (\ a → Vec (List (Fin a)) v') (lengthFun es es') vs'Rai

    isExt = subst (\ a → Vec (Fin a) i) (lengthFun es es') (mapV (extend (length es')) is)
    osExt = subst (\ a → Vec (Fin a) o) (lengthFun es es') (mapV (extend (length es')) os)

    is'Rai = subst (\ a → Vec (Fin a) i') (lengthFun es es') (mapV (raise (length es)) is')
    os'Rai = subst (\ a → Vec (Fin a) o') (lengthFun es es') (mapV (raise (length es)) os')


idGraph : {n : ℕ} → Graph n n {0}
idGraph {0} = emptyGraph
idGraph {suc n} = parallel id1 (idGraph {n})

-----------------------------
-- sequential composition
-----------------------------

-- either an element (Fin n) or a placeholder <>
data M (n : ℕ) : Set where
  <>  : M n
  [_] : Fin n → M n

sucM : {n : ℕ} → M n → M (suc n)
sucM <> = <>
sucM [ x ] = [ (suc x) ]

sucF : {n : ℕ} → Fin n → Fin (n +N 1)
sucF 0F = 0F
sucF (suc fi) = suc (sucF fi)

suF : {n : ℕ} → Fin n → Fin (suc n)
suF 0F = 0F
suF (suc n) = suc (suF n)

su : (m : ℕ) → m +N 1 ≡ suc m
su 0 = refl
su (suc m) rewrite su m = refl

plus0 : (m : ℕ) → m ≡ m +N 0
plus0 0 = refl
plus0 (suc m) rewrite sym (plus0 m) = refl

+assoc : (a b c : ℕ) → a +N (b +N c) ≡ (a +N b) +N c
+assoc 0 b c = refl
+assoc (suc a) b c = cong suc (+assoc a b c)

-- working through the connections at the composition boundary and identifying edges
join : {m : ℕ} → (edgL edgR : List Edge) → Vec (Fin (length edgL)) m → Vec (Fin (length edgR)) m
     → (Σ (List Edge) \ es  → Vec (M (length es))  ((length edgL) +N (length edgR)))
     →  Σ (List Edge) \ es' → Vec (M (length es')) ((length edgL) +N (length edgR))
join {0} edgL edgR vls vrs p = p
join {suc m} edgL edgR (vl ∷ vls) (vr ∷ vrs) p with join {m} edgL edgR vls vrs p
join {suc m} edgL edgR (vl ∷ vls) (vr ∷ vrs) p | ls' , vs' with lookup vs' (extend (length edgR) vl)
join {suc m} edgL edgR (vl ∷ vls) (vr ∷ vrs) p | ls' , vs' | <> with lookup vs' (raise (length edgL) vr)
join {suc m} edgL edgR (vl ∷ vls) (vr ∷ vrs) p | ls' , vs' | <> | <>
  = lookupL edgL vl ∷ ls' , updateAt (extend (length edgR) vl) (\ _ → [ 0F ])
                           (updateAt (raise  (length edgL) vr) (\ _ → [ 0F ]) (mapV sucM vs'))
join {suc m} edgL edgR (vl ∷ vls) (vr ∷ vrs) p | ls' , vs' | <> | [ x ]
  = ls' , updateAt (extend (length edgR) vl) (\ _ → [ x ]) vs'
join {suc m} edgL edgR (vl ∷ vls) (vr ∷ vrs) p | ls' , vs' | [ x ]
  = ls' , updateAt (raise (length edgL) vr) (\ _ → [ x ]) vs'


-- edges that don't connect to the composition boundary are preserved in the list of new edges
collE : (edgs : List Edge) → (es : List Edge)
  → Vec (M (length es)) (length edgs)
  → Σ (List Edge) \ es' → Vec (Fin (length (es' +L es))) (length edgs)
collE [] es [] = [] , []
collE (edg ∷ edgs) es (<> ∷ vs) with collE edgs es vs
... | es' , vs' = edg ∷ es' , 0F ∷ mapV suc vs'
collE (edg ∷ edgs) es ([ x ] ∷ vs) with collE edgs es vs
... | es' , vs' = es' , subst Fin (lengthFun es' es) (raise (length es') x) ∷ vs'

-- updating an edge
update : {n m : ℕ} → Vec (Fin m) n → Fin n → Fin m
update vs n = lookup vs n

-- sequential composition
series : {i m o' v v' : ℕ} → Graph i m {v} → Graph m o' {v'} → Graph i o' {v +N v'}
series {i}{m}{o'}{v}{v'} (gr es vs (is , os)) (gr es' vs' (is' , os'))
  = gr (proj₁ coll +L proj₁ j) (vsUpd +V vs'Upd) (isUpd , os'Upd) where

  j = join es es' os is' ([] , replicate <>)
  coll = collE (es +L es') (proj₁ j) (subst (\ a → Vec (M (length (proj₁ j))) a) (lengthFun es es') (proj₂ j))

  vsExt = mapV (\ l → mapL (extend (length es')) l) vs
  vs'Rai = mapV (\ l → mapL (raise (length es)) l) vs'
  
  vsUpd  = mapV (mapL (update (proj₂ coll))) (subst (\ a → Vec (List (Fin a)) v)  (lengthFun es es') vsExt)
  vs'Upd = mapV (mapL (update (proj₂ coll))) (subst (\ a → Vec (List (Fin a)) v') (lengthFun es es') vs'Rai)

  isExt  = (mapV (extend (length es')) is)
  os'Rai = (mapV (raise (length es)) os')

  isUpd  = mapV (update (proj₂ coll)) (subst (\ a → Vec (Fin a) i)  (lengthFun es es') isExt)
  os'Upd = mapV (update (proj₂ coll)) (subst (\ a → Vec (Fin a) o') (lengthFun es es') os'Rai)


2cap : Graph 0 4 {0}
2cap = gr (e ∷ e ∷ []) [] ([] , 0F ∷ 1F ∷ 1F ∷ 0F ∷ [])

testing = series (parallel id1 2cap)
                 (parallel cup (parallel cup id1))


{-
GRAPH : Category 0l 0l 0l
GRAPH = record
          { Obj = ℕ
          ; _⇒_ = \ i o → Graph i o
          ; _≈_ = _≡_
          ; id = idGraph
          ; _∘_ = \ gbc gab → series gab gbc
          ; assoc =  \ {_}{_}{_}{_}{f = f}{g}{h} → ass f g h
          ; identityˡ = \ {_}{_}{g} → idL g
          ; identityʳ = \ {_}{_}{g} → idR g
          ; equiv = record { refl = refl ; sym = sym ; trans = trans }
          ; ∘-resp-≈ = λ {refl refl → refl}
          } where

          idR : {i o v : ℕ}(g : Graph i o {v}) → series idGraph g ≡ g
          idR (gr es rvs rio) = {!!}
          
          idL : {i o v : ℕ}(g : Graph i o {v}) → series g idGraph ≡ subst (\ a → Graph i o {a}) (plus0 v) g
          idL (gr ls x x₁) = {!!}

          ass : {i m m' o vf vg vh : ℕ}(f : Graph i m {vf})(g : Graph m m' {vg})(h : Graph m' o {vh})
              → series f (series g h) ≡ subst (\ a → Graph i o {a}) (+-assoc vf vg vh) (series (series f g) h)
          ass (gr ls x x₁) (gr ls₁ x₂ x₃) (gr ls₂ x₄ x₅) = {!!}
      
-}
