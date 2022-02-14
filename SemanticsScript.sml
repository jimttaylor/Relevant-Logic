
open HolKernel Parse boolLib bossLib;

open GoldblattRLTheory RLRulesTheory;
open listTheory;
open pred_setTheory;
open numpairTheory string_numTheory;
     
val _ = new_theory "Semantics";


val _ = set_fixity "-->" (Infixr 490);
val _ = overload_on ("-->", “g_IMP”);

val _ = set_fixity "&" (Infixl 600); 
val _ = overload_on ("&", “g_AND”);

val _ = overload_on ("~", “g_NOT”);
    
val _ = overload_on ("τ", “g_tt”);

val _ = set_fixity "V" (Infixl 500);
val _ = overload_on ("V", “g_OR”);
    
val _ = set_fixity "<->" (Infixr 490);
val _ = overload_on ("<->", “g_DIMP”);
 
val _ = set_fixity "∘ᵣ" (Infixl 600);
val _ = overload_on ("∘ᵣ", “g_ICONJ”);


    
Datatype: R_FRAME = <| W: α set; Z: α; R:α -> α -> α -> bool; STAR: α -> α |>
End
                       
    
Definition Reduced_R_Frame_def:
  Reduced_R_Frame RF  ⇔
    (RF.Z ∈ RF.W) ∧

    (∀x. x ∈ RF.W ⇒ (RF.STAR x) ∈ RF.W) ∧ 
       
    (∀x. x ∈ RF.W ⇒ RF.R RF.Z x x) ∧
    (∀x x' y y' z z'.
        x ∈ RF.W ∧ y ∈ RF.W ∧  z ∈ RF.W ∧ 
        x' ∈ RF.W ∧ y' ∈ RF.W ∧  z' ∈ RF.W ∧ 
        RF.R RF.Z x' x ∧ RF.R RF.Z y' y ∧ RF.R RF.Z z z' ∧ 
        RF.R x y z ⇒ RF.R x' y' z')  ∧
        
    (∀x. x ∈ RF.W ⇒ RF.STAR (RF.STAR x) = x) ∧
    (∀ w x y. RF.R w x y ∧ x ∈ RF.W ∧ y ∈ RF.W ∧ w ∈ RF.W ⇒ RF.R w (RF.STAR y) (RF.STAR x)) ∧
    (* RF.R Conditions *)
    (∀x. x ∈ RF.W ⇒ RF.R x x x) ∧
    (∀x y z.
        x ∈ RF.W ∧ y ∈ RF.W ∧  z ∈ RF.W ∧ 
        RF.R x y z ⇒ RF.R y x z) ∧
    (∀w x y z a.
       x ∈ RF.W ∧ y ∈ RF.W ∧  z ∈ RF.W ∧ w ∈ RF.W ∧  a ∈ RF.W ∧
        RF.R w x a ∧ RF.R a y z ⇒
       (∃ b. RF.R x y b ∧ RF.R w b z ∧ b ∈ RF.W))
       
End


Theorem R_ZERO_EXISTS[simp] = Reduced_R_Frame_def |> iffLR |> cj 1
Theorem R_STAR_CLOSURE      = Reduced_R_Frame_def |> iffLR |> cj 2
(* Theorem R_R_CLOSURE         = Reduced_R_Frame_def |> iffLR |> cj 3 *)

Theorem R_R_ZERO_REFLEX     = Reduced_R_Frame_def |> iffLR |> cj 3
Theorem R_R_MONOTONE        = Reduced_R_Frame_def |> iffLR |> cj 4
Theorem R_STAR_INVERSE      = Reduced_R_Frame_def |> iffLR |> cj 5
Theorem R_STAR_DUAL         = Reduced_R_Frame_def |> iffLR |> cj 6

Theorem R_R_SELF_REFLEX     = Reduced_R_Frame_def |> iffLR |> cj 7
Theorem R_R_COMM            = Reduced_R_Frame_def |> iffLR |> cj 8
Theorem R_INTER_WORLD       = Reduced_R_Frame_def |> iffLR |> cj 9


val _ = overload_on ("|-", “goldblatt_provable”);

Definition CONJl_def:
  (CONJl [] = τ) ∧
  (CONJl [p] = p) ∧ 
  (CONJl (p::(q::lp)) = p & CONJl (q::lp))
End
        
Definition pENTAIL_def:
  pENTAIL Γ p ⇔
    ∃ γ. γ ≠ [] ∧ (set γ) ⊆ Γ ∧ |- ((CONJl γ) --> p)
End

val _ = set_fixity "|-^" (Infixr 490); 
Overload "|-^" = “pENTAIL”
        
Definition R_Theory_def:
  R_Theory θ ⇔
    (∀p. θ |-^ p ⇒ p ∈ θ)   
End

Definition Regular_def:
  Regular θ ⇔
    R_Theory θ ∧ (∀p. |- p ⇒ p ∈ θ)
End                                                                          
        
Definition Holds_def:
  (Holds RF VF w (g_VAR s) ⇔ w ∈ VF s ∧ w ∈ RF.W) ∧
  (Holds RF VF w (a & b) ⇔ Holds RF VF w a ∧ Holds RF VF w b) ∧
  (Holds RF VF w (~a) ⇔ ¬ Holds RF VF (RF.STAR w) a) ∧
  (Holds RF VF w (a --> b) ⇔ ∀x y. x ∈ RF.W ∧ y ∈ RF.W ∧ RF.R w x y ∧ Holds RF VF x a ⇒ Holds RF VF y b) ∧
  (Holds RF VF w τ ⇔ RF.R RF.Z RF.Z w)
End

Definition Hereditary_def:
  Hereditary RF VF ⇔
    ∀x y s. RF.R RF.Z x y ∧ x ∈ VF s ⇒ y ∈ VF s
End
     
Theorem Hereditary_Lemma:
  ∀ RF VF x y p.
    x ∈ RF.W ∧ y ∈ RF.W ∧ Reduced_R_Frame RF ∧ Hereditary RF VF ∧ Holds RF VF x p ∧ RF.R RF.Z x y ⇒
    Holds RF VF y p
Proof
  gen_tac >> gen_tac >>
  simp[Hereditary_def] >> Induct_on ‘p’ >> 
  simp[Holds_def] 
  >- metis_tac[]
  >- (rpt strip_tac >> gs[] >>
      rename [‘RF.R y a b’, ‘Holds _ _ a p’] >> 
      ‘RF.R x a b’ suffices_by metis_tac[] >>
      drule_then irule R_R_MONOTONE >> simp[] >> 
      qexistsl_tac [‘y’, ‘a’, ‘b’] >> 
      metis_tac[R_R_ZERO_REFLEX]
     ) 
  >- metis_tac[]
  >- (rw[] >>
      ‘RF.R RF.Z (RF.STAR y) (RF.STAR x)’ by (irule R_STAR_DUAL >> simp[]) >> 
      metis_tac[R_STAR_CLOSURE])
  >- (rw[] >>
      irule R_R_MONOTONE >> simp[] >>
      qexistsl_tac [‘RF.Z’, ‘x’, ‘y’] >> simp[] >>
      simp[R_R_ZERO_REFLEX, R_R_SELF_REFLEX]
      )
QED

Theorem OR_Holds:
  ∀ RF VF w A B. Reduced_R_Frame RF ∧ w ∈ RF.W ⇒ (Holds RF VF w (A V B) ⇔ Holds RF VF w A ∨ Holds RF VF w B)
Proof
  strip_tac >> gs[g_OR_def, Holds_def] >> metis_tac[R_STAR_INVERSE]
QED

Theorem R_INTER_WORLD_CONVERSE:
∀RF. Reduced_R_Frame RF ⇒
     ∀w x y z b. RF.R x y b ∧ RF.R w b z ∧ x ∈ RF.W ∧ y ∈ RF.W ∧ z ∈ RF.W ∧ w ∈ RF.W ∧ b ∈ RF.W 
                 ⇒ ∃a. RF.R w x a ∧ RF.R a y z ∧ a ∈ RF.W
Proof
  metis_tac[R_R_COMM, R_INTER_WORLD]
QED
        
Theorem Contraction_Lemma:
  Reduced_R_Frame RF ∧ RF.R a b c ∧ a ∈ RF.W ∧ b ∈ RF.W ∧ c ∈ RF.W ⇒ ∃x. x ∈ RF.W ∧ RF.R a b x ∧ RF.R x b c 
Proof
  metis_tac[R_R_SELF_REFLEX, R_INTER_WORLD_CONVERSE]
QED
        
Theorem Soundness:
  |- p ∧ Reduced_R_Frame RF ∧ Hereditary RF VF ⇒ Holds RF VF RF.Z p 
Proof
  Induct_on ‘goldblatt_provable’ >> simp[Holds_def] >> rpt strip_tac
  >- metis_tac[Hereditary_Lemma, R_R_ZERO_REFLEX]
  >- (rename [‘RF.R RF.Z ab bc_ac’, ‘RF.R bc_ac bc ac’, ‘RF.R ac a c’] >> 
      ‘RF.R bc ab ac’ by
        (irule R_R_MONOTONE >> 
         metis_tac[R_R_ZERO_REFLEX, R_R_COMM]) >>
      metis_tac[R_INTER_WORLD]
     )
  >- (rename[‘RF.R RF.Z a ab_b’, ‘RF.R ab_b ab b’] >> 
      ‘RF.R a ab b’ by
        (irule R_R_MONOTONE >> 
         metis_tac[R_R_ZERO_REFLEX]) >> 
      metis_tac[R_R_COMM]
     )
  >- (rename [‘RF.R RF.Z abb ab’, ‘RF.R ab a b’] >> 
      last_x_assum irule>> simp[] >> qexistsl_tac [‘a’, ‘a’] >> simp[] >>
      irule Contraction_Lemma >> simp[] >>
      irule R_R_MONOTONE >> 
      metis_tac[R_R_ZERO_REFLEX, R_R_COMM]
     )
  >- metis_tac[Hereditary_Lemma]
  >- metis_tac[Hereditary_Lemma]
  >- (rename [‘RF.R RF.Z x y’, ‘RF.R y a b’] >> 
      last_x_assum irule >> simp[] >> qexists_tac ‘a’ >> gs[] >> 
      irule R_R_MONOTONE >> metis_tac[R_R_ZERO_REFLEX]
     )
  >- (rename [‘RF.R RF.Z x y’, ‘RF.R y a c’] >> 
      last_x_assum irule >> simp[] >> qexists_tac ‘a’ >> gs[] >> 
      irule R_R_MONOTONE >> metis_tac[R_R_ZERO_REFLEX]
     )
  >- metis_tac[OR_Holds, Hereditary_Lemma]
  >- metis_tac[OR_Holds, Hereditary_Lemma]
  >- (rename [‘RF.R RF.Z x y’, ‘RF.R y avb c’] >>
      ‘RF.R x avb c’ by
        (irule R_R_MONOTONE >> metis_tac[R_R_ZERO_REFLEX]) >>
      metis_tac[OR_Holds]
     )
  >- metis_tac[OR_Holds, Holds_def, Hereditary_Lemma]
  >- (rename [‘RF.R RF.Z x y’, ‘RF.R y b a’] >>
      ‘RF.R x (RF.STAR a) (RF.STAR b)’ by
        (irule R_R_MONOTONE >>  metis_tac[R_R_ZERO_REFLEX, R_STAR_DUAL, R_STAR_CLOSURE]) >>
      last_x_assum $ qspecl_then [‘RF.STAR a’, ‘RF.STAR b’] strip_assume_tac >> gs[] >>
      metis_tac [R_STAR_INVERSE, R_STAR_CLOSURE]
      )
  >- metis_tac[R_STAR_INVERSE, Hereditary_Lemma]
  >- (last_x_assum irule >> metis_tac[R_R_SELF_REFLEX, R_ZERO_EXISTS]
     )
  >- (irule Hereditary_Lemma >> simp[] >>
      qexists_tac ‘RF.Z’ >> gs[] >>
      irule R_R_MONOTONE >> simp[] >>
      qexistsl_tac [‘RF.Z’, ‘x’, ‘y’] >> simp[] >> strip_tac >> 
      assume_tac R_R_ZERO_REFLEX >> pop_assum $ qspec_then ‘RF’ irule >> simp[]
     )
  >- (last_x_assum irule >> metis_tac[R_R_SELF_REFLEX, R_ZERO_EXISTS]
     )
QED

Definition Prime_def:
  Prime θ ⇔
    R_Theory θ ∧ (∀A B. (A V B) ∈ θ ⇒ (A ∈ θ ∨ B ∈ θ))
End

Definition Consistent_def:
  Consistent θ ⇔
    R_Theory θ ∧ ¬∃A. A ∈ θ ∧ (~A) ∈ θ
End

Definition Ordinary_def:
  Ordinary θ ⇔ Prime θ ∧ Regular θ
End
        
Definition Normal_def:
  Normal θ ⇔ Ordinary θ ∧ Consistent θ
End

Definition Maximal_Excluding_def:
  Maximal_Excluding θ p ⇔
    ¬(θ |-^ p) ∧ ∀q. q ∉ θ ⇒ (θ ∪ {q}) |-^ p  
End


        
Definition R_gn:
  R_gn (g_VAR s) = 4*(s2n s + 1) ∧
  R_gn (A --> B) = 4*(R_gn A ⊗ R_gn B) + 1 ∧ 
  R_gn (A & B) = 4*(R_gn A ⊗ R_gn B) + 2 ∧
  R_gn (~A) = 4*(R_gn A) + 3 ∧ 
  R_gn τ = 0  
End

Theorem R_gn_INJ[simp]:
  ∀A B. R_gn A = R_gn B ⇔ A = B
Proof
  simp[EQ_IMP_THM] >> Induct >>
  Cases_on ‘B’ >> simp[R_gn] >> rpt strip_tac >>
  pop_assum (mp_tac o AP_TERM “flip (MOD) 4”) >> simp[]
QED
        
Theorem countable_g_props:
  countable 𝕌(:g_prop)
Proof
  simp[countable_def, INJ_DEF] >> metis_tac[R_gn_INJ]
QED

Definition Theta_i_def:
  Theta_i 0 A = {p | |- p} ∧ 
  Theta_i (SUC n) A =
  let p = LINV R_gn UNIV n;
      θ = Theta_i n A 
  in if θ ∪ {p} |-^ A
     then θ
     else θ ∪ {p}
End

Definition Theta_def:
  Theta A = BIGUNION {Theta_i n A | n ∈ UNIV}
End

Theorem Theta_i_grows:
  e ∈ Theta_i n A ∧ n ≤ m ⇒ e ∈ Theta_i m A
Proof
  rpt strip_tac >> Induct_on ‘m’
  >- (rpt strip_tac >> gs[Theta_i_def])
  >> Cases_on ‘n = SUC m’ >> strip_tac
  >- gs[]
  >> ‘n ≤ m’ by decide_tac >> gs[Theta_i_def] >> 
  Cases_on ‘Theta_i m A ∪ {LINV R_gn 𝕌(:g_prop) m} |-^ A’ >> gs[]
QED
        
Theorem FINITE_SUBSET_THETA:
  ∀s. FINITE s ⇒ (s ⊆ Theta A ⇔ ∃n. s ⊆ Theta_i n A)
Proof
  Induct_on ‘FINITE’ >> simp[] >> 
  rpt strip_tac >> simp[Theta_def, PULL_EXISTS] >> reverse eq_tac
  >- metis_tac[]
  >> rpt strip_tac >> rename [‘ e ∈ Theta_i m A’, ‘s ⊆ Theta_i n A’] >> 
  Cases_on ‘m ≤ n’
  >- metis_tac[Theta_i_grows]
  >> ‘n < m’ by decide_tac >>
  qexists_tac ‘m’ >> simp[SUBSET_DEF] >> rpt strip_tac
  >> irule Theta_i_grows >> qexists_tac ‘n’ >> gs[] >> 
  metis_tac[SUBSET_DEF]
QED

Theorem FINITE_SUBSET_UNION_THETA:
  ∀s. FINITE s ⇒ (s ⊆ (Theta A ∪ Q) ⇔ ∃n. s ⊆ (Theta_i n A ∪ Q) )
Proof
  Induct_on ‘FINITE’ >> simp[] >> 
  rpt strip_tac >> simp[Theta_def, PULL_EXISTS] >> reverse eq_tac
  >- metis_tac[]
  >> rpt strip_tac
  >- (rename [‘e ∈ Theta_i m A’, ‘s ⊆ Theta_i n A ∪ Q’] >> 
      Cases_on ‘m ≤ n’
      >- metis_tac[Theta_i_grows]
      >> ‘n < m’ by decide_tac >>
      qexists_tac ‘m’ >> simp[SUBSET_DEF] >> rpt strip_tac >> 
      Cases_on ‘x ∈ Q’
      >- simp[]
      >- (‘x ∈ Theta_i m A’ suffices_by simp[]
          >> irule Theta_i_grows >> qexists_tac ‘n’ >> gs[SUBSET_DEF] >> 
          metis_tac[]
         )
     )
  >- metis_tac[]
QED

        
Theorem LIST_SUBSET_ADJUNCTION:
  ∀γ. set γ ⊆ {p | |- p} ⇒ |- (CONJl γ)
Proof
  rpt strip_tac >> gs[SUBSET_DEF] >>
  Induct_on ‘γ’
  >- metis_tac[goldblatt_provable_rules, CONJl_def]
  >> Cases_on ‘γ’ >> gs[CONJl_def] >> 
  rpt strip_tac >> rename[‘|- (k & CONJl (h::t))’] >> 
  metis_tac[goldblatt_provable_rules]
QED

Theorem Theta_not_pENTAIL:
  ¬( |- A) ⇒ ¬ (Theta A |-^ A)
Proof
  rpt strip_tac >> gs[pENTAIL_def, FINITE_DEF, FINITE_SUBSET_THETA] >>
  Induct_on ‘n’ >> CCONTR_TAC >> gs[Theta_i_def]
  >- metis_tac [LIST_SUBSET_ADJUNCTION, goldblatt_provable_rules]
  >> Cases_on ‘Theta_i n A ∪ {LINV R_gn 𝕌(:g_prop) n} |-^ A’ >> gs[] >>
  qpat_x_assum ‘¬(Theta_i n A ∪ {LINV R_gn 𝕌(:g_prop) n} |-^ A)’ mp_tac >> 
  gs[pENTAIL_def] >> qexists_tac ‘γ’ >> gs[]
QED
        
Theorem Theta_Maximal_Rejection:
  ∀A. ¬ |- A ⇒ Maximal_Excluding (Theta A) A  
Proof
  simp [Maximal_Excluding_def] >> rpt strip_tac
  >- gs[Theta_not_pENTAIL]
  >- (‘¬(Theta A |-^ A)’ by gs[Theta_not_pENTAIL] >> CCONTR_TAC >>  
      qpat_x_assum ‘q ∉ Theta A’ mp_tac >> gs[] >>
      assume_tac FINITE_SUBSET_THETA >>
      last_x_assum $ qspec_then ‘{q}’ strip_assume_tac >> gs[] >> 
      qexists_tac ‘SUC (R_gn q)’ >> gs[Theta_i_def] >>
      ‘¬ (Theta_i (R_gn q) A ∪ {LINV R_gn 𝕌(:g_prop) (R_gn q)} |-^ A)’ suffices_by (
        gs[] >> rpt strip_tac >> 
        ‘q = LINV R_gn 𝕌(:g_prop) (R_gn q)’ by (
          ‘q ∈ 𝕌(:g_prop)’ by simp[] >>
          ‘INJ R_gn 𝕌(:g_prop)  𝕌(:num)’ by simp[INJ_DEF] >>
          metis_tac [LINV_DEF]
          ) >> simp[]
        ) >> gs[pENTAIL_def] >> rpt strip_tac >>
      ‘q = LINV R_gn 𝕌(:g_prop) (R_gn q)’ by (
        ‘q ∈ 𝕌(:g_prop)’ by simp[] >>
        ‘INJ R_gn 𝕌(:g_prop)  𝕌(:num)’ by simp[INJ_DEF] >>
        metis_tac [LINV_DEF]
        ) >> CCONTR_TAC >> gs[] >>
      qpat_x_assum ‘∀γ. γ = [] ∨ ¬(set γ ⊆ Theta A ∪ {q}) ∨ ¬|- (CONJl γ --> A)’ mp_tac >> gs[] >>
      qexists_tac ‘γ’ >> simp[] >> simp[SUBSET_DEF] >>
      rpt strip_tac >> ‘x ∈ Theta_i (R_gn q) A ∪ {q}’ by metis_tac[SUBSET_DEF] >> 
      gs[] >> assume_tac FINITE_SUBSET_THETA >>
      last_x_assum $ qspec_then ‘{x}’ strip_assume_tac >> gs[] >> 
      metis_tac[]                                                                          
     )
QED

Theorem g_imp_conj_rule:
  |- (A --> B) ∧ |- (A --> C) ⇒ |- (A --> (B & C))
Proof
  metis_tac[goldblatt_provable_rules]
QED

Theorem CONJl_weaken_r:
  γ ≠ [] ⇒ |- (CONJl (δ ++ γ) --> CONJl γ)
Proof
  Induct_on ‘δ’
  >- simp[g_identity]
  >- (Cases_on ‘δ’
      >- (Cases_on ‘γ’ >> gs[] >> 
          simp[CONJl_def, g_conjunction_r]
         )
      >- (gs[CONJl_def] >> rpt strip_tac
          >> metis_tac[goldblatt_provable_rules]
         )
     )
QED
        
Theorem CONJl_weaken_l:
  ∀δ. δ ≠ [] ⇒ |- (CONJl (δ ++ γ) --> CONJl δ)
Proof
  Induct_on ‘δ’
  >- simp[g_identity]
  >- (Cases_on ‘δ’
      >- (Cases_on ‘γ’ >> gs[] >> 
          simp[CONJl_def, g_identity, g_conjunction_l]
         )
      >- (gs[CONJl_def] >> rpt strip_tac
          >> metis_tac[goldblatt_provable_rules]
         )
     )
QED

Theorem CONJl_CONS_imp:
  |- (CONJl (h :: γ) --> h)
Proof
  Cases_on ‘γ’ >> simp[CONJl_def, g_identity, g_conjunction_l]
QED

Theorem NOT_MEM_FILTER_LEMMA:
  ∀ a γ. ¬ MEM a (FILTER (λx. x ≠ a) γ) 
Proof
  strip_tac >> Induct >> gs[] >> rw[]
QED
        
Theorem MEM_FILTER_LEMMA:
  ∀ a x γ. MEM x (FILTER (λx. x ≠ a) γ) ⇒ MEM x γ 
Proof
  Induct_on ‘γ’ >> gs[] >> rw[]
  >> metis_tac[] 
QED

Theorem Trans_pENTAILS:
  ∀ A p q. A |-^ p ∧ (A ∪ {p}) |-^ q ∧ {p | |- p } ⊆ A ⇒ A |-^ q  
Proof
  rpt strip_tac >>
  Cases_on ‘p ∈ A’ (* 2 *)
  >- (‘(A ∪ {p}) = A’ by (simp[EXTENSION] >> metis_tac[]) >> 
      metis_tac[]
     )
  >- (gs[pENTAIL_def] >> rename [‘|- (CONJl δ --> q)’] >>
      reverse $ Cases_on ‘MEM p δ’ (* 2 *)
      >- (qexists_tac ‘δ’ >> gs[SUBSET_DEF] >> rpt strip_tac >> 
          ‘x ≠ p’ by metis_tac[] >>
          qpat_x_assum ‘∀x. MEM x δ ⇒ x ∈ A ∨ x = p’ (qspec_then ‘x’ strip_assume_tac) >> 
          metis_tac[]
         )
      >- (qexists_tac ‘(FILTER (λ x. x ≠ p) δ) ++ γ’ >> strip_tac (* 2 *)
          >- (gs[SUBSET_DEF, MEM_FILTER, DISJ_IMP_THM] >> metis_tac[]
             )
          >- (‘|- (CONJl (FILTER (λx. x ≠ p) δ ⧺ γ) --> CONJl δ)’ suffices_by
                (rpt strip_tac
                 >- (gs[SUBSET_DEF] >> rw[] >> gs[] >> 
                     Cases_on ‘x = p’ >> gs[NOT_MEM_FILTER_LEMMA] >>
                     metis_tac[MEM_FILTER_LEMMA]
                    )
                 >- (metis_tac[g_suffixing, g_modus_ponens]
                    )
                ) >> Cases_on ‘γ = []’ >> gvs[CONJl_def] >> 
              qpat_x_assum ‘MEM p δ’ mp_tac >>
              qpat_x_assum ‘set δ ⊆ A ∪ {p}’ mp_tac >>
              qid_spec_tac ‘δ’ >> Induct >>
              gs[] >> rw[] >> rename[‘_ --> CONJl (h::Δ)’] >> gs[] (* 3 *)
              >- (‘CONJl (h :: Δ) = h & CONJl Δ’ by (
                   Cases_on ‘Δ’ >> gs[CONJl_def]
                   ) >> simp[] >> irule g_imp_conj_rule >> 
                  simp [CONJl_CONS_imp] >> 
                  ‘CONJl (h :: (FILTER (λx. x ≠ p) Δ ⧺ γ)) = h & (CONJl (FILTER (λx. x ≠ p) Δ ⧺ γ))’ by
                    (Cases_on ‘FILTER (λx. x ≠ p) Δ ⧺ γ’ >> gs[CONJl_def]
                    ) >> gs[] >> 
                  metis_tac[g_conjunction_r, g_suffixing, g_modus_ponens]
                 )
              >- (Cases_on ‘MEM h Δ’ >> gvs[]
                  >- (‘CONJl (h :: Δ) = h & CONJl Δ’ by (
                       Cases_on ‘Δ’ >> gs[CONJl_def]
                       ) >> simp[] >> irule g_imp_conj_rule >>
                      metis_tac[CONJl_weaken_r, g_suffixing, g_modus_ponens]
                     )
                  >- (‘FILTER (λx. x ≠ h) Δ = Δ’ by (
                       Induct_on ‘Δ’ >> rw[]
                       ) >> simp[] >> Cases_on ‘Δ = []’ >> gs[CONJl_def] >> 
                      ‘CONJl (h :: Δ) = h & CONJl Δ’ by (
                        Cases_on ‘Δ’ >> gs[CONJl_def]
                        ) >> simp[] >> irule g_imp_conj_rule >> strip_tac
                      >- metis_tac[CONJl_weaken_r, g_suffixing, g_modus_ponens]
                      >- simp[CONJl_weaken_l]
                     )
                 )
              >- (‘CONJl (h :: Δ) = h & CONJl Δ’ by (
                   Cases_on ‘Δ’ >> gs[CONJl_def]
                   ) >> simp[] >> irule g_imp_conj_rule >> 
                  metis_tac[CONJl_weaken_r, g_suffixing, g_modus_ponens]
                 )
             )   
         )
     )
QED

Theorem R_SUBSET_THETA:
 {p | |- p} ⊆ Theta A
Proof
  simp [SUBSET_DEF] >> rpt strip_tac >>
  ‘{x} ⊆ Theta_i 0 A’ by simp[Theta_i_def, SUBSET_DEF] >>
  ‘FINITE {x}’ by simp[] >>
  assume_tac FINITE_SUBSET_THETA >>
  last_x_assum $ qspec_then ‘{x}’ strip_assume_tac
  >> gs[] >> metis_tac[]
QED
          
Theorem Theta_R_Theory:
  ∀A. ¬ |- A ⇒ R_Theory (Theta A)  
Proof
  simp[R_Theory_def] >> rpt strip_tac >> 
  CCONTR_TAC >> ‘Maximal_Excluding (Theta A) A’ by metis_tac[Theta_Maximal_Rejection] >>
  gs[Maximal_Excluding_def] >> last_x_assum $ qspec_then ‘p’ strip_assume_tac >> gs[] >>
  metis_tac[R_SUBSET_THETA, Trans_pENTAILS]             
QED

Theorem CONJl_MEM_IMP:
  MEM p γ ⇒ |- (CONJl γ --> p)
Proof
  Induct_on ‘γ’ >> rw[]
  >- (Cases_on ‘γ = []’ >> gs[CONJl_def, g_identity] >>
      ‘CONJl (h::γ) = h & CONJl γ’ by
        (Cases_on ‘γ’ >> gs[CONJl_def]) >> simp[g_conjunction_l]
     )
  >- (gs[] >>
      ‘CONJl (h::γ) = h & CONJl γ’ by
        (Cases_on ‘γ’ >> gs[CONJl_def]) >> simp[] >> metis_tac[goldblatt_provable_rules]
     )
QED

Theorem IMP_MEM_IMP_CONJl:
  ∀q γ. (γ ≠ [] ∧ ∀p. (MEM p γ ⇒ |- (q --> p))) ⇒ |-(q --> CONJl γ) 
Proof
  rpt strip_tac >> 
  Induct_on ‘γ’ >> rw[] >> Cases_on ‘γ = []’
  >- gs[CONJl_def]
  >- (gs[] >>
      ‘CONJl (h::γ) = h & CONJl γ’ by
        (Cases_on ‘γ’ >> gs[CONJl_def]) >> simp[] >>
      irule g_imp_conj_rule >> gs[]
     )
QED

Theorem CONJl_IN_R_Theory_IMP:
  ∀ A γ. R_Theory A ∧ γ ≠ []  ⇒ (CONJl γ ∈ A ⇔ set γ ⊆ A) 
Proof
  gs[R_Theory_def, EQ_IMP_THM, SUBSET_DEF] >> rpt strip_tac >> last_x_assum $ irule >> gs[pENTAIL_def] (* 2 *)
  >- (qexists_tac ‘[CONJl γ]’ >> gs[CONJl_def, CONJl_MEM_IMP])
  >- (qexists_tac ‘γ’ >> gs[g_identity, SUBSET_DEF])
QED

Theorem Exists_Theta_prop:
  ∀A a. ¬( |- A ) ∧ a ∉ Theta A ⇒
         ∃ c. |- ((c & a) --> A) ∧ c ∈ Theta A
Proof
  rpt strip_tac >> ‘Maximal_Excluding (Theta A) A’ by simp[Theta_Maximal_Rejection] >>
  gs[Maximal_Excluding_def] >> last_x_assum $ qspec_then ‘a’ strip_assume_tac >> gs[pENTAIL_def] >>
  qexists_tac ‘CONJl (FILTER (λx. x ≠ a) γ)’ >> rw[] (* 2 *)
  >- (‘|- (CONJl (FILTER (λx. x ≠ a) γ) & a --> CONJl γ)’ suffices_by
        metis_tac[goldblatt_provable_rules] >>
      reverse $ Cases_on ‘MEM a γ’ (* 2 *)
      >- (‘set γ ⊆ Theta A’ by (
           gs[SUBSET_DEF] >> metis_tac[]
           ) >> metis_tac[]
         )
      >- (‘|- (CONJl (FILTER (λx. x ≠ a) γ) & a --> CONJl γ)’ suffices_by
            metis_tac[goldblatt_provable_rules] >> 
          Cases_on ‘FILTER (λx. x ≠ a) γ = []’ (* 2 *)
          >- (Induct_on ‘γ’ >> rw[CONJl_def] 
              >> gs[] >> Cases_on ‘γ = []’ >> gs[CONJl_def] (* 3 *)
              >- metis_tac[goldblatt_provable_rules]
              >- (‘CONJl (a::γ) = a & CONJl γ’ by
                    (Cases_on ‘γ’ >> gs[CONJl_def]) >> simp[] >>
                  irule g_imp_conj_rule >> simp[g_conjunction_r] >> 
                  last_x_assum irule >> strip_tac >>
                  ‘MEM a γ’ by
                    (Induct_on ‘γ’ >> rw[]) >> simp[] >>
                  ‘|- (CONJl γ --> CONJl (a::γ))’ suffices_by
                    metis_tac[goldblatt_provable_rules] >>
                  simp[] >> irule g_imp_conj_rule >> simp[g_identity, CONJl_MEM_IMP] 
                 )
              >- (‘CONJl (a::γ) = a & CONJl γ’ by
                    (Cases_on ‘γ’ >> gs[CONJl_def]) >> simp[] >>
                  irule g_imp_conj_rule >> simp[g_conjunction_r] >> 
                  last_x_assum irule >>
                  ‘|- (CONJl γ --> CONJl (a::γ))’ suffices_by
                    metis_tac[goldblatt_provable_rules] >>
                  simp[] >> irule g_imp_conj_rule >> simp[g_identity, CONJl_MEM_IMP]
                 )
             )
          >- (irule IMP_MEM_IMP_CONJl >> reverse $ strip_tac >> gs[] >>              
              rpt strip_tac >> Cases_on ‘p = a’
              >- metis_tac [goldblatt_provable_rules]
              >- (‘MEM p (FILTER (λx. x ≠ a) γ)’ suffices_by 
                    metis_tac[goldblatt_provable_rules, CONJl_MEM_IMP] >> 
                  qpat_x_assum ‘MEM p γ’ $ mp_tac >>
                  qid_spec_tac ‘γ’ >> Induct >> gs[] >>
                  rename [‘MEM p δ ⇒ MEM p (FILTER (λx. x ≠ a) δ)’] >> 
                  reverse $ rw[] >> gs[]
                 )   
             )
         )
     )
  >- (‘set (FILTER (λx. x ≠ a) γ) ⊆ Theta A’ suffices_by (
       rw[] >> ‘R_Theory (Theta A)’ by simp[Theta_R_Theory] >> 
       assume_tac CONJl_IN_R_Theory_IMP >>
       pop_assum $ qspecl_then [‘Theta A’, ‘FILTER (λx. x ≠ a) γ’] strip_assume_tac >>
       Cases_on ‘FILTER (λx. x ≠ a) γ = []’ >> gs[CONJl_def] >>
       ‘|- τ’ by metis_tac[goldblatt_provable_rules] >>
       assume_tac R_SUBSET_THETA >> gs[ SUBSET_DEF]
       ) >> 
      gs[SUBSET_DEF] >> rw[] >>
      Cases_on ‘x = a’ >> metis_tac[NOT_MEM_FILTER_LEMMA, MEM_FILTER_LEMMA]
     )
QED

        
Theorem Theta_Ordinary:
  ∀A. ¬ |- A ⇒ Ordinary (Theta A)  
Proof
  simp [Ordinary_def, Prime_def, Regular_def] >>
  rpt strip_tac
  >> simp[Theta_R_Theory]
  >- (rename[‘a V b ∈ Theta A’] >> CCONTR_TAC >> qpat_x_assum ‘a V b ∈ Theta A’ mp_tac >> gs[] >>
      assume_tac Exists_Theta_prop >> last_assum $ qspecl_then [‘A’, ‘a’] strip_assume_tac >> 
      last_x_assum $ qspecl_then [‘A’, ‘b’] strip_assume_tac >> gs[] >> 
      rename [‘|- (d & b --> A)’, ‘a V b ∉ Theta A’] >>
      ‘|- ((c & d) & a --> A)’ by (
        ‘|- (((c & d) & a) --> (c & a))’ by
           (assume_tac g_conj_introduction >>
            last_x_assum $ qspecl_then [‘((c & d) & a)’, ‘c’,‘a’] strip_assume_tac >> 
            metis_tac [g_conjunction_l, g_conjunction_r, g_modus_ponens,
                       g_conj_introduction, g_suffixing, g_adjunction_rule]
           ) >>
        metis_tac[g_suffixing, g_modus_ponens]
        ) >> 
      ‘|- ((c & d) & b --> A)’ by (
        ‘|- (((c & d) & b) --> (d & b))’ by
           (assume_tac g_conj_introduction >>
            last_x_assum $ qspecl_then [‘((c & d) & b)’, ‘c’, ‘b’] strip_assume_tac >> 
            metis_tac [g_conjunction_l, g_conjunction_r, g_modus_ponens,
                       g_conj_introduction, g_suffixing, g_adjunction_rule]
           ) >>
        metis_tac[g_suffixing, g_modus_ponens]
        ) >> 
      ‘(c & d) ∈ Theta A’ by (
        ‘R_Theory (Theta A)’ by simp [Theta_R_Theory] >>
        gs[R_Theory_def] >> last_x_assum irule >>
        simp[pENTAIL_def] >> qexists_tac ‘[c; d]’ >> gs[CONJl_def] >> simp[g_identity]
        ) >>                         
      ‘|- (((c & d) & (a V b)) --> A)’ by 
        metis_tac [g_suffixing, g_modus_ponens, g_adjunction_rule, g_distribution, g_disjunction_elim] >> 
      CCONTR_TAC >> gs[] >>
      ‘(Theta A) |-^ A’ by
        (simp[pENTAIL_def] >>
         qexists_tac ‘[(c & d); (a V b)]’ >> simp[CONJl_def]
        ) >>  
      metis_tac[Maximal_Excluding_def, Theta_Maximal_Rejection]
     )
  >- (assume_tac R_SUBSET_THETA >> gs[SUBSET_DEF]
     )   
QED
        
Definition sENTAILS_def:
  sENTAILS S Γ p ⇔
    ∃ γ. γ ≠ [] ∧ (set γ) ⊆ Γ ∧ (CONJl γ) --> p ∈ S
End
           
Definition S_Theory_def:
  S_Theory S Θ ⇔
    Ordinary S ∧ ∀p. (sENTAILS S Θ p ⇒ p ∈ Θ) 
End

Definition APPLYING_def:
  APPLYING X Y = {p | ∃γ. γ ≠ [] ∧ (CONJl γ --> p) ∈ X ∧ set γ ⊆ Y}
End

Definition Canonical_Frame_def:
  Canonical_Frame A =
    <|W := {w | Prime w ∧ S_Theory (Theta A) w};
      Z := (Theta A);
      R := λ x y z. APPLYING x y ⊆ z ∧ x ∈ {w | Prime w ∧ S_Theory (Theta A) w} ∧ 
                    y ∈ {w | Prime w ∧ S_Theory (Theta A) w} ∧
                    z ∈ {w | Prime w ∧ S_Theory (Theta A) w};
      STAR := λ x. {A | ~A ∉ x} |>
End
        
Theorem Canonical_Frame_STAR_STAR:
  ∀ A x.
    let C = Canonical_Frame A in 
      x ∈ C.W ⇒
      C.STAR (C.STAR x) = x
Proof
  simp [Canonical_Frame_def] >> 
  rpt strip_tac >> gs[EXTENSION] >> rw[EQ_IMP_THM] >>
  rename[‘~~a ∈ x’] >> gs[Prime_def, R_Theory_def] >> last_x_assum $ irule >>
  simp[pENTAIL_def] (* 2 *)
  >- (qexists_tac ‘[~~a]’ >> simp[SUBSET_DEF, g_double_negation, CONJl_def])
  >- (qexists_tac ‘[a]’ >> simp[SUBSET_DEF, g_double_neg, CONJl_def])
QED

Theorem CONJl_NOTIN_PRIME:
  ∀A γ. Prime A ∧ ~CONJl γ ∈ A ∧ γ ≠ [] ⇒
        ∃x. MEM x γ ∧ ~x ∈ A
Proof
  strip_tac >> Induct >> rw[] >> 
  Cases_on ‘γ = []’
  >- (qexists_tac ‘h’ >> gs[CONJl_def])
  >- (‘CONJl (h::γ) = h & CONJl (γ)’ by (Cases_on ‘γ’ >> gs[CONJl_def]) >>
      gs[] >>
      ‘(~h V ~CONJl γ) ∈ A’ by (
        gs[Prime_def, R_Theory_def] >> last_x_assum irule >>
        simp[pENTAIL_def] >> qexists_tac ‘[~(h & CONJl γ)]’ >> gs[CONJl_def, g_OR_def] >>
        ‘|- ((~(~~h & ~~CONJl γ)) <-> (~(h & CONJl γ)))’ by (
          ‘|- (h <-> ~~h)’ by simp[g_double_negative_equiv] >> 
          ‘|- (CONJl γ <-> ~~CONJl γ)’ by simp[g_double_negative_equiv] >> 
          metis_tac[g_equiv_AND, g_equiv_replacement, g_equiv_commutative]
          ) >> metis_tac[g_DIMP_def, g_modus_ponens, g_conjunction_r, g_conjunction_l]
        ) >> 
        gs[Prime_def] >> last_x_assum $ qspecl_then [‘~h’, ‘~ CONJl γ’] strip_assume_tac >>
        gs[] >>  metis_tac[]                    
     )
QED

Theorem Prime_STAR_R_Theory:
  ∀x. Prime x ⇒ R_Theory {A | ~A ∉ x}
Proof
  simp[R_Theory_def, pENTAIL_def] >> rpt strip_tac >> 
  CCONTR_TAC >>
  qpat_x_assum ‘|- (CONJl γ --> p)’ mp_tac >> gs[] >>
  Induct_on ‘γ’ 
  >- gs[]
  >- (Cases_on ‘γ = []’
      >- (gs[CONJl_def] >> rpt strip_tac >>
          ‘|- (~p --> ~h)’ by metis_tac[g_contrapositive_alt, g_equiv_replacement] >>
          gs[Prime_def, R_Theory_def, pENTAIL_def] >> qpat_x_assum ‘~h ∉ x’ mp_tac >> gs[] >> 
          last_x_assum irule >> qexists_tac ‘[~p]’ >>
          simp[CONJl_def, SUBSET_DEF]
         )
      >- (rpt strip_tac >>
          ‘CONJl (h::γ) = h & CONJl γ’ by (Cases_on ‘γ’ >> gs[CONJl_def]) >>
          gs[] >>
          ‘|- (~p --> ~(h & CONJl γ))’ by  
            metis_tac[goldblatt_provable_rules, g_contrapositive_alt, g_DIMP_def] >> 
          ‘~h V ~CONJl γ ∈ x’ by
            (gs[R_Theory_def, Prime_def] >> last_x_assum irule >> simp[pENTAIL_def] >>
             qexists_tac ‘[~p]’ >> simp[SUBSET_DEF, CONJl_def] >>
             simp[g_OR_def] >>
             ‘|- ((~(~~h & ~~CONJl γ)) <-> (~(h & CONJl γ)))’ by (
               ‘|- (h <-> ~~h)’ by simp[g_double_negative_equiv] >> 
               ‘|- (CONJl γ <-> ~~CONJl γ)’ by simp[g_double_negative_equiv] >> 
               metis_tac[g_equiv_AND, g_equiv_replacement, g_equiv_commutative]
               ) >> metis_tac[g_equiv_replacement, g_equiv_commutative]               
            ) >> 
          assume_tac CONJl_NOTIN_PRIME >> pop_assum $ qspecl_then [‘x’, ‘γ’] strip_assume_tac >> gs[Prime_def] >> 
          qpat_x_assum ‘∀A B. A V B ∈ x ⇒ A ∈ x ∨ B ∈ x’ $ qspecl_then [‘~h’, ‘~ CONJl γ’] strip_assume_tac >>
          gs[SUBSET_DEF] 
         )
     )
QED 

Theorem Theta_Theta_theory:
  ∀A. ¬ |- A ⇒  S_Theory (Theta A) (Theta A)
Proof
  rpt strip_tac >> 
  ‘Ordinary (Theta A)’ by simp[Theta_Ordinary] >> 
   rw[S_Theory_def, sENTAILS_def] >> gs[Ordinary_def, Prime_def] >>
   ‘CONJl γ ∈ Theta A’ by gs[CONJl_IN_R_Theory_IMP] >> gs[R_Theory_def] >>
   last_x_assum irule >> simp[pENTAIL_def] >> qexists_tac ‘[CONJl γ; CONJl γ --> p]’ >>
   simp[CONJl_def] >> simp[g_AND_MP]
QED

Theorem STAR_IN_CANONICAL_FRAME:
  ∀A x.
    let C = Canonical_Frame A in 
      x ∈ C.W ∧ ¬ |- A ⇒
      {A | ~A ∉ x} ∈ C.W
Proof               
  rpt strip_tac >> gs[Canonical_Frame_def] >> rpt strip_tac
  >- (simp[Prime_def] >> reverse $ rw[] (* 2 *)
      >- (rename [‘~(a V b) ∉ x’] >> CCONTR_TAC >> gs[g_OR_def] >> 
          ‘let C = Canonical_Frame A in
             C.STAR (C.STAR x) = x’ by
            (assume_tac Canonical_Frame_STAR_STAR >> gs[] >>
             pop_assum irule >> simp[Canonical_Frame_def]
             ) >> gs[S_Theory_def] >>
          ‘(~a & ~b) ∈ x’ by 
            (last_x_assum $ irule >> gs[sENTAILS_def] >>
             qexists_tac ‘[~a; ~b]’ >> rw[CONJl_def] >>
             gs[Regular_def, Ordinary_def] >> last_x_assum irule >> 
             simp[g_identity]    
            ) >> 
          gs[EXTENSION, Canonical_Frame_def]
         )
      >- simp[Prime_STAR_R_Theory]                                                                
     )
  >- (gs[S_Theory_def, sENTAILS_def] >> rw[] >> CCONTR_TAC >>
      gs[] >> ‘S_Theory (Theta A) (Theta A)’ by gs[Theta_Theta_theory] >> gs[S_Theory_def] >> 
      ‘~p --> ~CONJl γ ∈ Theta A’ by
        (last_x_assum irule >> simp[sENTAILS_def] >>
         qexists_tac ‘[CONJl γ --> p]’ >> simp[CONJl_def] >>
         ‘|- ((CONJl γ --> p) --> ~p --> ~CONJl γ)’ by
           metis_tac[goldblatt_provable_rules, g_contrapositive_alt, g_DIMP_def] >> 
         gs[Ordinary_def, Regular_def]
        ) >>
      qpat_x_assum ‘set γ ⊆ {A | ~A ∉ x}’ mp_tac >> simp[SUBSET_DEF] >>
      ‘~CONJl γ ∈ x’ by
        (last_x_assum irule >> simp[sENTAILS_def] >>
         qexists_tac ‘[~p]’ >> gs[SUBSET_DEF, CONJl_def]
        ) >>      
        gs[CONJl_NOTIN_PRIME]
     )
QED


Definition B_WORLD_i_def:
  B_WORLD_i 0 Θ S R= S ∧
  B_WORLD_i (SUC n) Θ S R=
  let p = LINV R_gn UNIV n;
      B_WORLD_n = B_WORLD_i n Θ S R
  in if (∃A. A ∈ R ∧ sENTAILS Θ (B_WORLD_n ∪ {p}) A)  
     then B_WORLD_n
     else B_WORLD_n ∪ {p}   
End

Definition B_WORLD_def:
  B_WORLD Θ S R = BIGUNION {B_WORLD_i n Θ S R | n ∈ UNIV}
End
        
Theorem B_WORLD_i_grows:
  ∀ e n m Θ A R. e ∈ B_WORLD_i n Θ A R ∧ n ≤ m ⇒
                 e ∈ B_WORLD_i m Θ A R
Proof
  rpt strip_tac >> Induct_on ‘m’
  >- (rpt strip_tac >> gs[B_WORLD_i_def])
  >> Cases_on ‘n = SUC m’ >> strip_tac
  >- gs[]
  >> ‘n ≤ m’ by decide_tac >> gs[B_WORLD_i_def] >> rw[]
QED
        
Theorem FINITE_SUBSET_B_WORLD:
    ∀ s Θ A R. FINITE s ⇒ (s ⊆ B_WORLD Θ A R ⇔ ∃n. s ⊆ B_WORLD_i n Θ A R)
Proof
  Induct_on ‘FINITE’ >> simp[] >> 
  rpt strip_tac >> simp[B_WORLD_def, PULL_EXISTS] >> reverse eq_tac
  >- metis_tac[]
  >> rpt strip_tac >>
  rename [‘e ∈ B_WORLD_i m Θ I' R’,
          ‘s ⊆ B_WORLD_i n Θ I' R’] >> 
  Cases_on ‘m ≤ n’
  >- metis_tac[B_WORLD_i_grows]
  >> ‘n < m’ by decide_tac >>
  qexists_tac ‘m’ >> simp[SUBSET_DEF] >> rpt strip_tac >>
  irule B_WORLD_i_grows >> qexists_tac ‘n’ >> gs[] >> 
  metis_tac[SUBSET_DEF]
QED
 
Theorem CONJl_split:
  ∀ α β. α ≠ [] ∧ β ≠ [] ⇒
         |- (CONJl α & CONJl β --> CONJl (α ++ β)) ∧
         |- (CONJl (α ++ β) --> CONJl α & CONJl β)
Proof
  rw[]
  >- (Induct_on ‘α’ >> rw[] >>
      Cases_on ‘α = []’ >> rw[CONJl_def] 
      >- (‘CONJl (h::β) = h & CONJl β’ by (Cases_on ‘β’ >> metis_tac[CONJl_def]) >>
          gs[g_identity]
         )
      >- (‘CONJl (h::α) = h & CONJl α’ by (Cases_on ‘α’ >> metis_tac[CONJl_def]) >>
          ‘CONJl (h::(α ⧺ β)) = h & CONJl (α ++ β)’ by (Cases_on ‘α ++ β’ >> gs[] >> metis_tac[CONJl_def]) >> 
          gs[] >>
          ‘|- (h & CONJl α & CONJl β --> CONJl α & CONJl β)’ by
            metis_tac[g_suffixing, g_modus_ponens, g_conj_introduction, g_conjunction_l, g_conjunction_r, g_adjunction_rule] >>
          ‘|- (h & CONJl α & CONJl β --> h)’ by  
            metis_tac[g_suffixing, g_modus_ponens, g_conjunction_l] >>
          metis_tac[g_adjunction_rule, g_conj_introduction, g_modus_ponens, g_suffixing]
         )
     )
  >- (Induct_on ‘α’ >> rw[] >>
      Cases_on ‘α = []’
      >- (‘CONJl (h::β) = h & CONJl β’ by (Cases_on ‘β’ >> metis_tac[CONJl_def]) >>
          gs[g_identity, CONJl_def])
      >- (‘CONJl (h::α) = h & CONJl α’ by (Cases_on ‘α’ >> metis_tac[CONJl_def]) >>
          ‘CONJl (h::(α ⧺ β)) = h & CONJl (α ++ β)’ by (Cases_on ‘α ++ β’ >> gs[] >> metis_tac[CONJl_def]) >> 
          gs[] >>
          ‘|- (h & (CONJl α & CONJl β) --> h & CONJl α & CONJl β)’ by
            metis_tac[g_suffixing, g_modus_ponens, g_conj_introduction, g_conjunction_l, g_conjunction_r, g_adjunction_rule] >>
          ‘|- (h & CONJl (α ⧺ β) --> (CONJl α & CONJl β))’ by  
            metis_tac[g_conjunction_r, g_modus_ponens, g_suffixing] >>
          metis_tac[g_conjunction_l, g_conj_introduction, g_modus_ponens, g_adjunction_rule, g_suffixing]
         )
     )
QED

        
Theorem S_Theory_imp_R_Theory:
  ∀ θ x. S_Theory θ x ⇒ R_Theory x
Proof
  rpt strip_tac >>
  gs[R_Theory_def, S_Theory_def, pENTAIL_def, sENTAILS_def] >>
  rpt strip_tac >> last_x_assum irule >>
  qexists_tac ‘γ’ >> 
  gs[Ordinary_def, Regular_def]
QED

Theorem CONJl_split_equiv:
  ∀ α β. α ≠ [] ∧ β ≠ [] ⇒
         |- (CONJl α & CONJl β <-> CONJl (α ++ β))
Proof
  metis_tac[g_DIMP_def, goldblatt_provable_rules, CONJl_split]
QED


Theorem CONJl_IN_APPLIED:
  ∀ θ w x γ. S_Theory θ w ∧  
             set γ ⊆ APPLYING w x ∧ γ ≠ [] ⇒
             CONJl γ ∈ APPLYING w x
Proof
  rw[] >> Induct_on ‘γ’ >> rw[] >>
  Cases_on ‘γ = []’
  >- metis_tac[CONJl_def]
  >- (gs[] >>
      ‘CONJl (h::γ) = h & CONJl γ’ by
        (Cases_on ‘γ’ >> metis_tac[CONJl_def]
        ) >> gs[APPLYING_def] >>
      rename[‘CONJl α --> CONJl γ ∈ w’, ‘CONJl β --> h’, ‘CONJl (h::γ) = h & CONJl γ’] >> 
      qexists_tac ‘α ++ β’ >> simp[CONJl_def] >>
      ‘(CONJl α & CONJl β) --> h ∈ w ∧ (CONJl α & CONJl β) --> CONJl γ ∈ w’ by
        (‘R_Theory w’ by metis_tac[S_Theory_imp_R_Theory] >> gs[R_Theory_def, pENTAIL_def] >>
         strip_tac (* 2 *)
         >- (last_x_assum irule >> qexists_tac ‘[CONJl β --> h]’ >> simp[CONJl_def, g_AND_STRENGTHEN])
         >- (last_x_assum irule >> qexists_tac ‘[CONJl α --> CONJl γ]’ >> simp[CONJl_def, g_AND_STRENGTHEN])
        ) >>             
      gs[S_Theory_def, sENTAILS_def] >> last_x_assum irule >>
      qexists_tac ‘[CONJl α & CONJl β --> h; CONJl α & CONJl β --> CONJl γ]’ >> rw[CONJl_def] >> 
      gs[Ordinary_def, Regular_def] >> last_x_assum irule >>
      ‘|- ((CONJl α & CONJl β --> h) & (CONJl α & CONJl β --> CONJl γ) -->
           CONJl α & CONJl β --> h & CONJl γ)’ by simp[g_conj_introduction] >>
      ‘|- (CONJl α & CONJl β --> (CONJl α & CONJl β --> h) & (CONJl α & CONJl β --> CONJl γ) -->
            h & CONJl γ)’ by metis_tac[g_permutation, g_modus_ponens] >>
      ‘|- (CONJl (α ++ β) --> CONJl α & CONJl β)’ by simp[CONJl_split] >> 
      metis_tac[g_suffixing, g_modus_ponens, g_permutation]
     )
QED


Theorem g_imp_conj_introduction:
  ∀ A B C D. |-  (A --> B --> C) ∧ |-  (A --> B --> D) ⇒
             |- (A --> B --> (C & D))
Proof
  rpt strip_tac >>
  ‘|- ((A ∘ᵣ B) --> C)’ by metis_tac[g_io_rule] >> 
  ‘|- ((A ∘ᵣ B) --> D)’  by metis_tac[g_io_rule] >>
  ‘|- ((A ∘ᵣ B) --> C & D)’  suffices_by metis_tac[g_io_rule] >>
  metis_tac[goldblatt_provable_rules] 
QED


Theorem IMP_CONJl_R_THEORY:
  ∀ A γ θ. γ ≠ [] ∧ R_Theory θ ∧ (∀ B. B ∈ set γ ⇒ A --> B ∈ θ) ⇒
           A --> CONJl γ ∈ θ 
Proof
  rw[] >> Induct_on ‘γ’ >> rw[] >>
  Cases_on ‘γ = []’
  >- gs[CONJl_def]
  >- (‘CONJl (h::γ) = h & CONJl γ’ by
        (Cases_on ‘γ’ >> gs[CONJl_def]) >>
      gs[R_Theory_def, pENTAIL_def] >> last_x_assum irule >>
      qexists_tac ‘[A --> h; A --> CONJl γ]’ >>
      gs[CONJl_def, g_conj_introduction]
     )
QED

Theorem g_A_CONJl_A:
  ∀A γ. set γ ⊆ {A} ∧ γ ≠ []  ⇒
        |- (A --> CONJl γ)
Proof
  rw[] >> Induct_on ‘γ’ >> rw[] >>
  Cases_on ‘γ = []’ >> gs[CONJl_def, g_identity] >>
  ‘CONJl (A::γ) = A & CONJl γ’ by (Cases_on ‘γ’ >> gs[CONJl_def]) >>
  metis_tac [goldblatt_provable_rules]                                                            
QED

Theorem EMPTY_FILTER_LEMMA:
  ∀a γ. FILTER (λx. x ≠ a) γ = [] ⇔ set γ ⊆ {a}  
Proof
  rw[EQ_IMP_THM, SUBSET_DEF] >> 
  Induct_on ‘γ’ >> rw[] >> gs[]
QED


Theorem FILTER_AND_FILTERED_IMP_CONJl:
  ∀A γ. γ ≠ [] ∧ MEM A γ ∧ FILTER (λx. x ≠ A) γ ≠ [] ⇒ 
          |- ((CONJl (FILTER (λx. x ≠ A) γ) & A) --> CONJl γ)
Proof
  rw[] >>
  Induct_on ‘γ’ >> rw[] (* 3 *)
  >- (Cases_on ‘FILTER (λx. x ≠ A) γ = []’ >> gs[CONJl_def] (* 2*)
      >- (‘set γ ⊆ {A}’ by metis_tac[EMPTY_FILTER_LEMMA] >>
          Cases_on ‘γ = []’
          >- metis_tac[goldblatt_provable_rules, CONJl_def]
          >- (‘CONJl (h::γ) = h & CONJl γ’ by (Cases_on ‘γ’ >> gs[CONJl_def]) >>
              gs[] >> metis_tac[goldblatt_provable_rules, g_A_CONJl_A]
             )
         )
      >- (Cases_on ‘γ = []’ >> rw[CONJl_def] (* 2 *)
          >- metis_tac[goldblatt_provable_rules]
          >- (‘CONJl (h::FILTER (λx. x ≠ A) γ) = h & CONJl (FILTER (λx. x ≠ A) γ)’ by
                (Cases_on ‘FILTER (λx. x ≠ A) γ’ >> gs[CONJl_def]
                ) >>
              ‘CONJl (h::γ) = h & CONJl γ’ by (Cases_on ‘γ’ >> gs[CONJl_def]) >>
              gs[] >>
              ‘|- (h & CONJl (FILTER (λx. x ≠ A) γ) & A --> h & (CONJl (FILTER (λx. x ≠ A) γ) & A))’ by 
                gs[g_AND_associative_rl] >>
              ‘|- (h & (CONJl (FILTER (λx. x ≠ A) γ) & A) --> h & CONJl γ)’ by
                metis_tac[goldblatt_provable_rules] >>
              metis_tac[g_suffixing, g_modus_ponens]
             )
         )
     )
  >- (Cases_on ‘γ = []’ >>
      Cases_on ‘MEM A γ’ >> gs[] 
      >- (‘CONJl (A::γ) = A & CONJl γ’ by (Cases_on ‘γ’ >> gs[CONJl_def]) >>
          gs[] >> metis_tac[goldblatt_provable_rules]
         )
      >- (‘FILTER (λx. x ≠ A) γ = γ’ by
            (Induct_on ‘γ’ >> rw[] >> gs[] >>
             Cases_on ‘γ = []’ >> gs[] >>
             Cases_on ‘FILTER (λx. x ≠ A) γ = []’ >> gs[] >>
             ‘∃B. MEM B γ’ by (Cases_on ‘γ’ >> gs[]) >>
             Induct_on ‘γ’ >> gs[]
            ) >>
          ‘CONJl (A::γ) = A & CONJl γ’ by (Cases_on ‘γ’ >> gs[CONJl_def]) >> 
          gs[] >> metis_tac[goldblatt_provable_rules]
         )
     )
  >- (Cases_on ‘γ = []’ >> gs[] >>
      ‘CONJl (A::γ) = A & CONJl γ’ by (Cases_on ‘γ’ >> gs[CONJl_def]) >>
      gs[] >> metis_tac[goldblatt_provable_rules]
     )
QED

Theorem FILTER_NON_MEM_EQUAL:
  ∀ γ A. ¬MEM A γ ⇒ FILTER (λx. x ≠ A) γ = γ
Proof
  Induct_on ‘γ’ >> rw[] >> gs[] >>
  Cases_on ‘γ = []’ >> gs[] >>
  Cases_on ‘FILTER (λx. x ≠ A) γ = []’ >> gs[] >>
  ‘∃B. MEM B γ’ by (Cases_on ‘γ’ >> gs[]) >>
  Induct_on ‘γ’ >> gs[]
QED

        
Theorem Maximal_S_Theory_APP_prop_exists:
  ∀ θ w x B a. S_Theory θ w ∧ Prime w ∧ a ∉ x ∧
               S_Theory θ x ∧ x ≠ ∅ ∧ ¬sENTAILS θ (APPLYING w x) B ∧
               (∀E. E ∉ x ⇒ sENTAILS θ (APPLYING w (x ∪ {E})) B) ⇒
               ∃c γ. c ∈ x ∧ c & a --> CONJl γ ∈ w ∧ CONJl γ --> B ∈ θ 
Proof
  rpt strip_tac >> last_x_assum $ qspec_then ‘a’ strip_assume_tac >> gs[sENTAILS_def] >>
  assume_tac CONJl_IN_APPLIED >>
  pop_assum $ qspecl_then [‘θ’, ‘w’, ‘x ∪ {a}’, ‘γ’] strip_assume_tac >> 
  gs[APPLYING_def] >> rename[‘set δ ⊆ x ∪ {a}’] >>
  ‘∃b. b ∈ x’ by simp[MEMBER_NOT_EMPTY] >> 
  qexistsl_tac [‘CONJl (b::(FILTER (λx. x ≠ a) δ))’, ‘γ’] >> rw[] (* 2 *)  
  >- (‘set (b::FILTER (λx. x ≠ a) δ) ⊆ x’ suffices_by (
       rw[] >> ‘R_Theory x’ by metis_tac[S_Theory_imp_R_Theory] >> 
       assume_tac CONJl_IN_R_Theory_IMP >>
       pop_assum $ qspecl_then [‘x’, ‘b::FILTER (λx. x ≠ a) δ’] strip_assume_tac >>
       Cases_on ‘FILTER (λx. x ≠ a) δ = []’ >> gs[CONJl_def]
       ) >> 
      gs[SUBSET_DEF] >> rw[] >> 
      Cases_on ‘x' = a’ >> metis_tac[NOT_MEM_FILTER_LEMMA, MEM_FILTER_LEMMA]
     )
  >- (‘CONJl (FILTER (λx. x ≠ a) δ) & a --> CONJl γ ∈ w’ suffices_by
        (rw[] >> Cases_on ‘FILTER (λx. x ≠ a) δ = []’ >> gs[CONJl_def] (* 2 *)
         >- (‘set δ ⊆ {a}’ by gs[EMPTY_FILTER_LEMMA] >>
             gs[S_Theory_def, sENTAILS_def] >> last_x_assum irule >>
             qexists_tac ‘[CONJl δ --> CONJl γ]’ >> rw[CONJl_def] >>
             qpat_x_assum ‘Ordinary θ’ mp_tac >> 
             rw[Ordinary_def, Regular_def, SUBSET_DEF] >> last_x_assum irule >>
             metis_tac[goldblatt_provable_rules, g_A_CONJl_A]
            )
         >- (‘CONJl (b::FILTER (λx. x ≠ a) δ) = b & CONJl (FILTER (λx. x ≠ a) δ)’ by
               (Cases_on ‘FILTER (λx. x ≠ a) δ’ >> gs[CONJl_def]) >>
             ‘R_Theory w’ by metis_tac [S_Theory_imp_R_Theory] >>
             gs[R_Theory_def, pENTAIL_def] >> last_assum irule >>
             qexists_tac ‘[CONJl (FILTER (λx. x ≠ a) δ) & a --> CONJl γ]’ >>
             rw[CONJl_def, g_AND_STRENGTHEN] >> irule g_modus_ponens >>
             qexists_tac
             ‘(b & (CONJl (FILTER (λx. x ≠ a) δ) & a) --> CONJl γ) -->
              (b & CONJl (FILTER (λx. x ≠ a) δ) & a --> CONJl γ)’ >>
             reverse $ strip_tac >> metis_tac[goldblatt_provable_rules, g_AND_associative_rl]
            )
        ) >>
      Cases_on ‘FILTER (λx. x ≠ a) δ = []’ (* 2 *)
      >- (‘set δ ⊆ {a}’ by gs[EMPTY_FILTER_LEMMA] >>
          ‘R_Theory w’ by metis_tac[S_Theory_imp_R_Theory] >>
          gs[R_Theory_def, pENTAIL_def] >> last_assum irule >>
          qexists_tac ‘[a --> CONJl γ]’ >> gs[g_AND_STRENGTHEN, CONJl_def] >>
          last_assum irule >> qexists_tac ‘[CONJl δ --> CONJl γ]’ >> gs[CONJl_def] >> 
          metis_tac[goldblatt_provable_rules, g_A_CONJl_A]
         )
      >- (‘R_Theory w’ by metis_tac[S_Theory_imp_R_Theory] >>
          gs[R_Theory_def, pENTAIL_def] >>
          pop_assum irule >> qexists_tac ‘[CONJl δ --> CONJl γ]’ >>
          gs[CONJl_def] >> irule g_modus_ponens >>
          qexists_tac ‘(CONJl (FILTER (λx. x ≠ a) δ) & a) --> CONJl δ’ >>
          gs[g_suffixing] >> Cases_on ‘MEM a δ’ (* 2 *)
          >- gs[FILTER_AND_FILTERED_IMP_CONJl]
          >- (‘FILTER (λx. x ≠ a) δ = δ’ by simp[FILTER_NON_MEM_EQUAL] >>
              gs[g_conjunction_l]
             )
         )
     )
QED

Theorem Maximal_S_Theory_APP_imp_prime:
  ∀ θ w x B. S_Theory θ w ∧ Prime w ∧ x ≠ ∅ ∧
             S_Theory θ x ∧ ¬sENTAILS θ (APPLYING w x) B ∧
             (∀E. E ∉ x ⇒ sENTAILS θ (APPLYING w (x ∪ {E})) B) ⇒
             Prime x
Proof
  rpt strip_tac >> rw[Prime_def]
  >- metis_tac[S_Theory_imp_R_Theory]
  >- (rename[‘C V D ∈ x’] >> CCONTR_TAC >>
      gs[] >> assume_tac Maximal_S_Theory_APP_prop_exists >>
      last_x_assum $ qspecl_then [‘θ’, ‘w’, ‘x’, ‘B’] strip_assume_tac >>
      gs[] >>
      first_assum $ qspec_then ‘C’ strip_assume_tac >>
      first_x_assum $ qspec_then ‘D’ strip_assume_tac >> 
      gs[] >>
      ‘CONJl γ V CONJl γ' --> B ∈ θ’ by
        (gs[S_Theory_def, Ordinary_def, R_Theory_def, Prime_def, pENTAIL_def] >>
         last_x_assum irule >>
         qexists_tac ‘[CONJl γ --> B; CONJl γ' --> B]’ >>
         gs[CONJl_def, g_disjunction_elim]
        ) >>
      rename[‘CONJl γ V CONJl δ --> B ∈ θ’, ‘d & D --> CONJl δ ∈ w’] >>
      qpat_x_assum ‘¬sENTAILS θ (APPLYING w x) B’ mp_tac >> gs[] >>
      ‘R_Theory w’ by metis_tac[S_Theory_imp_R_Theory] >> gs[R_Theory_def, pENTAIL_def] >>  
      ‘((c & d) & C) --> (CONJl γ V CONJl δ) ∈ w’ by
        (last_x_assum irule >>
         qexists_tac ‘[c & C --> CONJl γ]’ >> gs[CONJl_def] >>
         irule g_modus_ponens >>
         qexists_tac ‘c & d & C --> c & C’ >> rw[]
         >- metis_tac[goldblatt_provable_rules]
         >- (irule g_modus_ponens >>
             qexists_tac ‘CONJl γ --> CONJl γ V CONJl δ’ >> rw[]
             >- metis_tac[goldblatt_provable_rules]
             >- metis_tac[g_modus_ponens, g_permutation, g_suffixing]
            )
        ) >>
      ‘((c & d) & D) --> (CONJl γ V CONJl δ) ∈ w’ by
        (last_x_assum irule >>
         qexists_tac ‘[d & D --> CONJl δ]’ >> gs[CONJl_def] >>
         irule g_modus_ponens >>
         qexists_tac ‘c & d & D --> d & D’ >> rw[]
         >- metis_tac[goldblatt_provable_rules]
         >- (irule g_modus_ponens >>
             qexists_tac ‘CONJl δ --> CONJl γ V CONJl δ’ >> rw[]
             >- metis_tac[goldblatt_provable_rules]
             >- metis_tac[g_modus_ponens, g_permutation, g_suffixing]
            )
        ) >>
      ‘((c & d) & (C V D)) --> (CONJl γ V CONJl δ) ∈ w’ by
        (last_x_assum irule >>
         qexists_tac ‘[((c & d) & C) --> (CONJl γ V CONJl δ);
                       ((c & d) & D) --> (CONJl γ V CONJl δ)]’ >> 
         gs[CONJl_def] >>
         metis_tac [g_suffixing, g_modus_ponens, g_adjunction_rule, g_distribution, g_disjunction_elim]
        ) >>
      ‘c & d ∈ x’ by
        (‘R_Theory x’ by metis_tac[S_Theory_imp_R_Theory] >>
         gs[R_Theory_def, pENTAIL_def] >> last_x_assum irule >>
         qexists_tac ‘[c; d]’ >> gs[CONJl_def] >> simp[g_identity]
        ) >> simp[sENTAILS_def] >>
      qexists_tac ‘[CONJl γ V CONJl δ]’ >> gs[CONJl_def] >>
      simp[APPLYING_def] >> 
      qexists_tac ‘[c & d; C V D]’ >> gs[CONJl_def]
     )        
QED                                  


Theorem Maximal_S_Theory_prop_exists:
  ∀ θ x B a. a ∉ x ∧ S_Theory θ x ∧ x ≠ ∅ ∧ ¬sENTAILS θ x B ∧
             (∀E. E ∉ x ⇒ sENTAILS θ (x ∪ {E}) B) ⇒
             ∃c. c ∈ x ∧ c & a --> B ∈ θ 
Proof
  rpt strip_tac >> last_x_assum $ qspec_then ‘a’ strip_assume_tac >> gs[sENTAILS_def] >>
  ‘∃b. b ∈ x’ by gs[MEMBER_NOT_EMPTY] >> 
  qexists_tac ‘CONJl(b::FILTER (λx. x ≠ a) γ)’ >> rw[] (* 2 *)
  >- (‘set (b::FILTER (λx. x ≠ a) γ) ⊆ x’ suffices_by (
       rw[] >> ‘R_Theory x’ by metis_tac[S_Theory_imp_R_Theory] >> 
       assume_tac CONJl_IN_R_Theory_IMP >>
       pop_assum $ qspecl_then [‘x’, ‘b::FILTER (λx. x ≠ a) γ’] strip_assume_tac >>
       Cases_on ‘FILTER (λx. x ≠ a) γ = []’ >> gs[CONJl_def]
       ) >>
      gs[SUBSET_DEF] >> rw[] >> 
      Cases_on ‘x' = a’ >> metis_tac[NOT_MEM_FILTER_LEMMA, MEM_FILTER_LEMMA]
     )
  >- (‘CONJl (FILTER (λx. x ≠ a) γ) & a --> B ∈ θ’ suffices_by
        (rw[] >> Cases_on ‘FILTER (λx. x ≠ a) γ = []’ >> gs[CONJl_def] (* 2 *)
         >- (‘set γ ⊆ {a}’ by gs[EMPTY_FILTER_LEMMA] >>
             gs[S_Theory_def] >> 
             qpat_x_assum ‘Ordinary θ’ mp_tac >> 
             rw[Ordinary_def, Prime_def, R_Theory_def, SUBSET_DEF, pENTAIL_def] >> last_x_assum irule >>
             qexists_tac ‘[CONJl γ --> B]’ >> rw[CONJl_def] >>
             metis_tac[goldblatt_provable_rules, g_A_CONJl_A]
            )
         >- (‘CONJl (b::FILTER (λx. x ≠ a) γ) = b & CONJl (FILTER (λx. x ≠ a) γ)’ by
               (Cases_on ‘FILTER (λx. x ≠ a) γ’ >> gs[CONJl_def]) >>
             gs[S_Theory_def] >> 
             qpat_x_assum ‘Ordinary θ’ mp_tac >> 
             rw[Ordinary_def, Prime_def, R_Theory_def, SUBSET_DEF, pENTAIL_def] >> last_x_assum irule >> 
             qexists_tac ‘[CONJl (FILTER (λx. x ≠ a) γ) & a --> B]’ >>
             rw[CONJl_def, g_AND_STRENGTHEN] >> irule g_modus_ponens >>
             qexists_tac
             ‘(b & (CONJl (FILTER (λx. x ≠ a) γ) & a) --> B) -->
              (b & CONJl (FILTER (λx. x ≠ a) γ) & a --> B)’ >>
             reverse $ strip_tac >> metis_tac[goldblatt_provable_rules, g_AND_associative_rl]
            )
       ) >> 
      Cases_on ‘FILTER (λx. x ≠ a) γ = []’ (* 2 *)
      >- (‘set γ ⊆ {a}’ by gs[EMPTY_FILTER_LEMMA] >>
          ‘R_Theory θ’ by (gs[S_Theory_def, Ordinary_def, Prime_def]) >>
          gs[R_Theory_def, pENTAIL_def] >> last_assum irule >>
          qexists_tac ‘[a --> B]’ >> gs[g_AND_STRENGTHEN, CONJl_def] >>
          last_assum irule >> qexists_tac ‘[CONJl γ --> B]’ >> gs[CONJl_def] >> 
          metis_tac[goldblatt_provable_rules, g_A_CONJl_A]
         )
      >- (‘R_Theory θ’ by (gs[S_Theory_def, Ordinary_def, Prime_def]) >>
          gs[R_Theory_def, pENTAIL_def] >>
          pop_assum irule >> qexists_tac ‘[CONJl γ --> B]’ >>
          gs[CONJl_def] >> irule g_modus_ponens >>
          qexists_tac ‘(CONJl (FILTER (λx. x ≠ a) γ) & a) --> CONJl γ’ >>
          gs[g_suffixing] >> Cases_on ‘MEM a γ’ (* 2 *)
          >- gs[FILTER_AND_FILTERED_IMP_CONJl]
          >- (‘FILTER (λx. x ≠ a) γ = γ’ by simp[FILTER_NON_MEM_EQUAL] >>
              gs[g_conjunction_l]
             )
         )
     )
QED

Theorem Maximal_S_Theory_imp_prime:
  ∀ θ w x B. x ≠ ∅ ∧ S_Theory θ x ∧ ¬sENTAILS θ x B ∧
             (∀E. E ∉ x ⇒ sENTAILS θ (x ∪ {E}) B) ⇒
             Prime x
Proof
  rpt strip_tac >> rw[Prime_def]
  >- metis_tac[S_Theory_imp_R_Theory]
  >- (rename[‘C V D ∈ x’] >> CCONTR_TAC >>
      gs[] >> assume_tac Maximal_S_Theory_prop_exists >>
      last_x_assum $ qspecl_then [‘θ’, ‘x’, ‘B’] strip_assume_tac >>
      gs[] >>
      first_assum $ qspec_then ‘C’ strip_assume_tac >>
      first_x_assum $ qspec_then ‘D’ strip_assume_tac >> 
      gs[] >> qpat_x_assum ‘¬sENTAILS θ x B’ mp_tac >> simp[sENTAILS_def] >>
      qexists_tac ‘[c; c'; (C V D)]’ >> simp[CONJl_def] >>
      rename[‘c & (d & (C V D)) --> B ∈ θ’] >>
      gs[S_Theory_def, Ordinary_def, Prime_def, R_Theory_def, pENTAIL_def] >>
       ‘c & d & (C V D) --> B ∈ θ’ suffices_by
        (rw[] >> last_assum irule >>
         qexists_tac ‘[c & d & (C V D) --> B]’ >> gs[CONJl_def] >> 
         metis_tac [g_AND_associative_lr, g_modus_ponens, g_suffixing]
        ) >> 
      last_assum irule >>
      qexists_tac ‘[c & d & C --> B;  c & d & D --> B]’ >> rw[CONJl_def]
      >- (last_assum irule >> qexists_tac ‘[c & C --> B]’ >> simp[CONJl_def] >>
          metis_tac[goldblatt_provable_rules, g_permutation, g_AND_STRENGTHEN]
         )
      >- (last_assum irule >> qexists_tac ‘[d & D --> B]’ >> simp[CONJl_def] >>
          metis_tac[goldblatt_provable_rules, g_permutation, g_AND_STRENGTHEN]
         )
      >- metis_tac [g_suffixing, g_modus_ponens, g_adjunction_rule, g_distribution, g_disjunction_elim]
     )
QED
                                     
Theorem Canonical_Frame_is_R_Frame:
  ∀A.
    ¬ |-A ⇒ Reduced_R_Frame (Canonical_Frame A)
Proof
  simp[Reduced_R_Frame_def] >> rpt strip_tac >>
  gs[Canonical_Frame_def] >>
  ‘Ordinary (Theta A)’ by simp[Theta_Ordinary] (* 9 *)
  >- gs[Ordinary_def, Theta_Theta_theory]
  >- (‘{A | ~A ∉ x} ∈ (Canonical_Frame A).W’ by
        (assume_tac STAR_IN_CANONICAL_FRAME >> gs[] >> pop_assum irule
         >> simp[Canonical_Frame_def]
        ) >> gs[Canonical_Frame_def]
     )
  >- (gs[Theta_Theta_theory, Ordinary_def] >> rw[APPLYING_def, SUBSET_DEF] >>
      rename [‘p ∈ x’] >> gs[S_Theory_def, sENTAILS_def] >> last_x_assum irule >>
      qexists_tac ‘γ’ >> simp [SUBSET_DEF]
     )
  >- (‘Theta A ∈ (Canonical_Frame A).W’ by 
        gs[Theta_Theta_theory, Ordinary_def, Canonical_Frame_def] >> 
      gs[] >> 
      ‘x' ⊆ x’ by
        (gs[APPLYING_def, SUBSET_DEF] >> rw[] >> last_x_assum irule >> 
         rename [‘B ∈ t’] >> qexists_tac ‘[B]’ >> gs[CONJl_def, Ordinary_def, Regular_def, g_identity]
        ) >>
      ‘y' ⊆ y’ by
        (gs[APPLYING_def, SUBSET_DEF] >> rw[] >> last_x_assum irule >> 
         rename [‘B ∈ t’] >> qexists_tac ‘[B]’ >> gs[CONJl_def, Ordinary_def, Regular_def, g_identity]
        ) >> 
      ‘z ⊆ z'’ by 
        (gs[APPLYING_def, SUBSET_DEF] >> rw[] >> last_x_assum irule >> 
         rename [‘B ∈ t’] >> qexists_tac ‘[B]’ >> gs[CONJl_def, Ordinary_def, Regular_def, g_identity]
        ) >>
      ‘APPLYING x' y' ⊆ z’ suffices_by gs[SUBSET_DEF] >>
      rw[APPLYING_def, SUBSET_DEF] >> 
      rename [‘B ∈ z’] >> qpat_x_assum ‘APPLYING x y ⊆ z’ mp_tac >>
      rw[APPLYING_def, SUBSET_DEF] >> pop_assum irule >> qexists_tac ‘γ’ >>
      gs[SUBSET_DEF]
     )
  >- (rw[EXTENSION, EQ_IMP_THM] >> rename[‘~~a ∈ x’] >>
      gs[S_Theory_def] >> last_x_assum irule >> simp[sENTAILS_def]
      >- (qexists_tac ‘[~~a]’ >> simp[CONJl_def, SUBSET_DEF] >>
          gs[Ordinary_def, Regular_def, g_double_negation]
         )
      >- (qexists_tac ‘[a]’ >> simp[CONJl_def, SUBSET_DEF] >>
            gs[Ordinary_def, Regular_def, g_double_neg]
         )
     )
  >- (‘{A | ~A ∉ x} ∈ (Canonical_Frame A).W’ by
        (assume_tac STAR_IN_CANONICAL_FRAME >> gs[] >>
         pop_assum irule >> simp[Canonical_Frame_def]
        ) >> 
      ‘{A | ~A ∉ y} ∈ (Canonical_Frame A).W’ by
        (assume_tac STAR_IN_CANONICAL_FRAME >> gs[] >>
         pop_assum irule >> simp[Canonical_Frame_def]
        ) >> gs[] >> simp[APPLYING_def, SUBSET_DEF] >> 
      gs[Canonical_Frame_def] >> rpt strip_tac >> rename [‘~a ∈ x’] >>
      qpat_x_assum ‘∀x. MEM x γ ⇒ ~x ∉ y’ mp_tac >> gs[] >>
      ‘~a --> ~CONJl γ ∈ w’ by (
        qpat_x_assum ‘S_Theory (Theta A) w’ mp_tac >>
        rw[S_Theory_def, sENTAILS_def] >> pop_assum irule >>
        qexists_tac ‘[CONJl γ --> a]’ >> simp [CONJl_def, SUBSET_DEF] >>
        ‘|- ((CONJl γ --> a) --> ~a --> ~CONJl γ)’ suffices_by gs[Ordinary_def, Regular_def] >> 
        metis_tac[g_contrapositive_alt, g_DIMP_def, goldblatt_provable_rules]
        ) >>
      ‘~CONJl γ ∈ y’ by 
        (gs[APPLYING_def, SUBSET_DEF] >> last_x_assum irule >>
         qexists_tac ‘[~a]’ >> simp[CONJl_def]
        ) >> irule CONJl_NOTIN_PRIME >> gs[]
     )
  >- (rw[APPLYING_def, SUBSET_DEF] >> rename[‘a ∈ x’] >>
      gs[S_Theory_def, sENTAILS_def] >> last_x_assum irule >>
      qexists_tac ‘[CONJl γ; (CONJl γ --> a)]’ >> gs[CONJl_def] >>
      gs[CONJl_IN_R_Theory_IMP, Prime_def, g_AND_MP, Ordinary_def, Regular_def, SUBSET_DEF]
     )
  >- (rw[APPLYING_def, SUBSET_DEF] >> rename[‘a ∈ z’] >>
      qpat_x_assum ‘APPLYING x y ⊆ z’ mp_tac >> rw[APPLYING_def, SUBSET_DEF] >>
      pop_assum irule >> qexists_tac ‘[CONJl γ --> a]’ >> simp[CONJl_def] >>
      gs[S_Theory_def] >> last_x_assum irule >> simp[sENTAILS_def] >>
      qexists_tac ‘γ’ >> gs[SUBSET_DEF, Ordinary_def, Regular_def, g_assertion]
     )  
  >- (qexists_tac ‘B_WORLD (Theta A) (APPLYING x y) {p | (∃q. p --> q ∈ w ∧ q ∉ z)}’ >>
      ‘APPLYING x y ⊆
       B_WORLD (Theta A) (APPLYING x y) {p | (∃q. p --> q ∈ w ∧ q ∉ z)}’ by
        (rw[B_WORLD_def, BIGUNION, PULL_EXISTS, SUBSET_DEF] >> qexists_tac ‘0’ >>
         gs[B_WORLD_i_def]
        ) >> 
      ‘APPLYING w
       (B_WORLD (Theta A) (APPLYING x y) {p | (∃q. p --> q ∈ w ∧ q ∉ z)}) ⊆ z’ by (
        rw[Once SUBSET_DEF, Once APPLYING_def] >> 
        rename[‘β ∈ z’] >> assume_tac FINITE_SUBSET_B_WORLD >>
        pop_assum $ qspecl_then [‘set γ’, ‘Theta A’, ‘APPLYING x y’,
                                 ‘{p | (∃q. p --> q ∈ w ∧ q ∉ z)}’]
                  strip_assume_tac >> gs[] >> 
        Induct_on ‘n’ >> simp[B_WORLD_i_def]
        >- (rw[] >> ‘CONJl γ ∈ APPLYING x y’ by metis_tac[CONJl_IN_APPLIED] >> 
            pop_assum mp_tac >> 
            qpat_x_assum ‘APPLYING w x ⊆ a’ mp_tac >> 
            qpat_x_assum ‘APPLYING a y ⊆ z’ mp_tac >>
            rw[APPLYING_def, SUBSET_DEF] >> 
            last_x_assum irule >> qexists_tac ‘γ'’ >> 
            simp[] >> last_x_assum irule >>
            qexists_tac ‘[CONJl γ' --> CONJl γ]’ >> simp[CONJl_def] >>
            ‘|- ((CONJl γ --> β)  --> (CONJl γ' --> CONJl γ) --> CONJl γ' --> β)’ by
              metis_tac [goldblatt_provable_rules, g_permutation] >>
            gs[S_Theory_def] >> last_x_assum irule >> simp[sENTAILS_def] >>
            qexists_tac ‘[CONJl γ --> β]’ >> gs[CONJl_def, Ordinary_def, Regular_def]
           )
        >- (rw[] >> 
            CCONTR_TAC >>
            qpat_x_assum
            ‘¬∃A'.
                (∃q. A' --> q ∈ w ∧ q ∉ z) ∧
                sENTAILS (Theta A)
                         (B_WORLD_i n (Theta A) (APPLYING x y)
                          {p | (∃q. p --> q ∈ w ∧ q ∉ z)} ∪ {LINV R_gn 𝕌(:g_prop) n}) A'’ mp_tac >>
            simp[] >> qexists_tac ‘CONJl γ’ >> rw[]
            >- metis_tac[]
            >- (simp[sENTAILS_def] >> qexists_tac ‘γ’ >> gs[Ordinary_def, Regular_def, g_identity, CONJl_def]
               )
           )  
        ) >>
      ‘S_Theory (Theta A)
       (B_WORLD (Theta A) (APPLYING x y) {p | (∃q. p --> q ∈ w ∧ q ∉ z)})’ by
        (rw[S_Theory_def, sENTAILS_def] >> simp[B_WORLD_def, PULL_EXISTS] >>
         qexists_tac ‘SUC (R_gn p)’ >> simp[B_WORLD_i_def] >>
         ‘p = LINV R_gn 𝕌(:g_prop) (R_gn p)’ by (
           ‘p ∈ 𝕌(:g_prop)’ by simp[] >>
           ‘INJ R_gn 𝕌(:g_prop)  𝕌(:num)’ by simp[INJ_DEF] >>
           metis_tac [LINV_DEF]
           ) >> simp[PULL_EXISTS] >>
         ‘¬∃A' q.
             (A' --> q ∈ w ∧ q ∉ z) ∧
             sENTAILS (Theta A)
                      (B_WORLD_i (R_gn p) (Theta A) (APPLYING x y)
                       {p | (∃q. p --> q ∈ w ∧ q ∉ z)} ∪
                       {p}) A'’ suffices_by
           (rw[] >> metis_tac[]) >>
         CCONTR_TAC >> gs[sENTAILS_def] >> 
         rename [‘CONJl δ --> B ∈ Theta A’] >>
         ‘(B --> q) --> CONJl δ --> q ∈ Theta A’ by
           (qpat_x_assum ‘Ordinary (Theta A)’ mp_tac >>
            rw[Ordinary_def, Prime_def, R_Theory_def, pENTAIL_def] >>
            last_x_assum irule >> qexists_tac ‘[CONJl δ --> B]’ >> 
            simp[CONJl_def, g_suffixing] 
           ) >>
         ‘q ∈ APPLYING w
          (B_WORLD (Theta A) (APPLYING x y) {p | (∃q. p --> q ∈ w ∧ q ∉ z)})’ suffices_by
           metis_tac[SUBSET_DEF] >>
         simp[APPLYING_def] >>
         qexists_tac ‘(FILTER (λx. x ≠ p) δ) ++ γ’ >> reverse $ rw[]
         >- gs[APPLYING_def]
         >- (‘∀δ. set δ ⊆
                      B_WORLD_i (R_gn p) (Theta A) (APPLYING x y)
                      {p | (∃q. p --> q ∈ w ∧ q ∉ z)} ∪ {p} ⇒ 
                  set (FILTER (λx. x ≠ p) δ) ⊆
                      B_WORLD (Theta A) {p | (∃γ. γ ≠ [] ∧ CONJl γ --> p ∈ x ∧ set γ ⊆ y)}
                      {p | (∃q. p --> q ∈ w ∧ q ∉ z)}’ by
               (Induct >> rw[] >> assume_tac FINITE_SUBSET_B_WORLD >>
                pop_assum $ qspec_then ‘{h}’ strip_assume_tac >>
                gs[] >> qexists_tac ‘R_gn p’ >> gs[APPLYING_def]
               ) >>
             gs[]
            )
         >- (qpat_x_assum ‘S_Theory (Theta A) w’ mp_tac >> rw[S_Theory_def, sENTAILS_def] >>
             last_assum irule >> qexists_tac ‘[CONJl δ --> q]’ >> rw[CONJl_def]
             >- (last_x_assum irule >> qexists_tac ‘[B --> q]’ >> gs[CONJl_def]
                )
             >- (assume_tac Theta_Theta_theory >> pop_assum $ qspec_then ‘A’ mp_tac >>
                 rw[S_Theory_def, sENTAILS_def] >> last_assum irule >>
                 qexists_tac ‘[CONJl (FILTER (λx. x ≠ p) δ ⧺ γ) --> CONJl δ]’ >>
                 reverse $ rw[CONJl_def]
                 >- (qpat_x_assum ‘Ordinary (Theta A)’ mp_tac >>
                     rw[Ordinary_def, Regular_def] >>
                     pop_assum irule >> simp[g_suffixing]
                    )
                 >- (irule IMP_CONJl_R_THEORY >> gs[Theta_R_Theory] >>
                     rw[] >> rename [‘MEM b δ’] >> Cases_on ‘b = p’
                     >- (simp[] >>
                         Cases_on ‘FILTER (λx. x ≠ p) δ = []’ >> simp[] >>
                         assume_tac Theta_R_Theory >>
                         pop_assum $ qspec_then ‘A’ strip_assume_tac >>
                         gs[R_Theory_def, pENTAIL_def] >> pop_assum irule >>
                         qexists_tac ‘[CONJl γ --> p]’ >> simp[CONJl_def] >>
                         irule g_modus_ponens >> qexists_tac ‘CONJl (FILTER (λx. x ≠ p) δ) & CONJl γ --> CONJl γ’ >>
                         simp[g_conjunction_r] >>
                         metis_tac[g_modus_ponens, g_suffixing, g_permutation, CONJl_split]
                        )
                     >- (‘MEM b (FILTER (λx. x ≠ p) δ)’ by
                           (pop_assum mp_tac >> 
                            pop_assum mp_tac >>
                            qid_spec_tac ‘δ’ >>
                            qid_spec_tac ‘b’ >> 
                            qid_spec_tac ‘p’ >> 
                            gen_tac >> gen_tac >>
                            Induct >> rw[] >> CCONTR_TAC >> 
                            gs[]
                           ) >> 
                         assume_tac Theta_R_Theory >>
                         pop_assum $ qspec_then ‘A’ strip_assume_tac >>
                         gs[R_Theory_def, pENTAIL_def] >> pop_assum irule >>
                         qexists_tac ‘[CONJl (FILTER (λx. x ≠ p) δ) --> b]’ >>
                         rw[CONJl_def]
                         >- (gs[Ordinary_def, Regular_def] >> last_x_assum irule >>
                             gs[CONJl_MEM_IMP]
                            ) 
                         >- (irule g_modus_ponens >> qexists_tac ‘CONJl (FILTER (λx. x ≠ p) δ) & CONJl γ --> CONJl (FILTER (λx. x ≠ p) δ)’ >>
                             simp[g_conjunction_l] >> irule g_modus_ponens >>
                             qexists_tac ‘CONJl (FILTER (λx. x ≠ p) δ ⧺ γ) --> CONJl (FILTER (λx. x ≠ p) δ) & CONJl γ’ >>
                             ‘FILTER (λx. x ≠ p) δ ≠ []’ by (CCONTR_TAC >> gs[]) >> 
                             simp[CONJl_split] >> 
                             metis_tac[g_modus_ponens, g_suffixing, g_permutation]
                            )
                        )
                    )
                )
            ) 
        ) >> gs[] >> 
      rw[Prime_def]
      >- metis_tac[S_Theory_imp_R_Theory]
      >- (CCONTR_TAC >> gs[] >>
          rename[‘C V D ∈ B_WORLD (Theta A) (APPLYING x y) {p | (∃q. p --> q ∈ w ∧ q ∉ z)}’] >>
          qabbrev_tac ‘bw =  B_WORLD (Theta A) (APPLYING x y) {p | (∃q. p --> q ∈ w ∧ q ∉ z)}’ >> 
          drule_then drule Maximal_S_Theory_prop_exists >>
          simp[GSYM MEMBER_NOT_EMPTY, PULL_EXISTS] >>
          first_assum $ irule_at Any >> 
          cheat                                  
         )
     )
QED


        
Definition X_WORLD_i_def:
  X_WORLD_i 0 Θ S R w = S ∧
  X_WORLD_i (SUC n) Θ S R w =
  let p = LINV R_gn UNIV n;
      X_WORLD_n = X_WORLD_i n Θ S R w
  in if (∃A. A ∈ R ∧ sENTAILS Θ (APPLYING w (X_WORLD_n ∪ {p})) A)  
     then X_WORLD_n
     else X_WORLD_n ∪ {p}   
End

Definition X_WORLD_def:
  X_WORLD Θ S R w = BIGUNION {X_WORLD_i n Θ S R w | n ∈ UNIV}
End

Definition Y_WORLD_i_def:
  Y_WORLD_i 0 Θ S R = S ∧
  Y_WORLD_i (SUC n) Θ S R =
  let p = LINV R_gn UNIV n;
      Y_WORLD_n = Y_WORLD_i n Θ S R
  in if (∃A. A ∈ R ∧ sENTAILS Θ (Y_WORLD_n ∪ {p}) A)  
     then Y_WORLD_n
     else Y_WORLD_n ∪ {p}   
End

Definition Y_WORLD_def:
  Y_WORLD Θ S R = BIGUNION {Y_WORLD_i n Θ S R | n ∈ UNIV}
End


Theorem X_WORLD_i_grows:
  ∀ e n m Θ A R w. e ∈ X_WORLD_i n Θ A R w ∧ n ≤ m ⇒
                   e ∈ X_WORLD_i m Θ A R w
Proof
  rpt strip_tac >> Induct_on ‘m’
  >- (rpt strip_tac >> gs[X_WORLD_i_def])
  >> Cases_on ‘n = SUC m’ >> strip_tac
  >- gs[]
  >> ‘n ≤ m’ by decide_tac >> gs[X_WORLD_i_def] >> rw[]
QED
        
Theorem FINITE_SUBSET_X_WORLD:
  ∀s Θ A R w. FINITE s ⇒ (s ⊆ X_WORLD Θ A R w ⇔ ∃n. s ⊆ X_WORLD_i n Θ A R w)
Proof
  Induct_on ‘FINITE’ >> simp[] >> 
  rpt strip_tac >> simp[X_WORLD_def, PULL_EXISTS] >> reverse eq_tac
  >- metis_tac[]
  >> rpt strip_tac >>
  rename [‘e ∈ X_WORLD_i m Θ I' R w’,
          ‘s ⊆ X_WORLD_i n Θ I' R w’] >> 
  Cases_on ‘m ≤ n’
  >- metis_tac[X_WORLD_i_grows]
  >> ‘n < m’ by decide_tac >>
  qexists_tac ‘m’ >> simp[SUBSET_DEF] >> rpt strip_tac >>
  irule X_WORLD_i_grows >> qexists_tac ‘n’ >> gs[] >> 
  metis_tac[SUBSET_DEF]
QED

Theorem APPLYING_WORLDS:
  ∀ A γ w. γ ≠ [] ∧ set γ ⊆ APPLYING w {A} ∧ S_Theory θ w ∧ R_Theory w ⇒
             A --> CONJl γ ∈ w
Proof
  rw[APPLYING_def, SUBSET_DEF] >> Induct_on ‘γ’ >> rw[] >>
  Cases_on ‘γ = []’
  >- (gs[CONJl_def] >> assume_tac g_A_CONJl_A >>
      pop_assum $ qspecl_then [‘A’, ‘γ'’] strip_assume_tac >>
      gs[SUBSET_DEF, S_Theory_def, Ordinary_def, Regular_def] >>
      ‘(CONJl γ' --> h) --> A --> h ∈ θ’ by
        (last_x_assum irule >> irule g_modus_ponens >>
         qexists_tac ‘A --> CONJl γ'’ >> gs[] >>
         metis_tac [goldblatt_provable_rules, g_permutation]
        ) >> last_x_assum irule >>
      simp[sENTAILS_def] >>
      qexists_tac ‘[CONJl γ' --> h]’ >> simp[CONJl_def]
     )
  >- (‘CONJl (h::γ) = h & CONJl γ’ by (Cases_on ‘γ’ >> gs[CONJl_def]) >>
      gs[S_Theory_def] >>
      ‘A --> h ∈ w’ by
        (first_x_assum $ qspec_then ‘h’ strip_assume_tac >> 
         gs[CONJl_def] >> assume_tac g_A_CONJl_A >>
         pop_assum $ qspecl_then [‘A’, ‘γ'’] strip_assume_tac >>
         gs[SUBSET_DEF, S_Theory_def, Ordinary_def, Regular_def] >>
         ‘(CONJl γ' --> h) --> A --> h ∈ θ’ by
           (last_x_assum irule >> irule g_modus_ponens >>
            qexists_tac ‘A --> CONJl γ'’ >> gs[] >>
            metis_tac [goldblatt_provable_rules, g_permutation]
           ) >> last_x_assum irule >>
         simp[sENTAILS_def] >>
         qexists_tac ‘[CONJl γ' --> h]’ >> simp[CONJl_def]
        ) >> gs[R_Theory_def] >> first_x_assum irule >>
      simp[pENTAIL_def] >> qexists_tac ‘[A --> h; A --> CONJl γ]’ >>
      simp[CONJl_def, g_conj_introduction]
     )
QED

Theorem APPLIED_X_WORLD_i_GROWS:
  ∀ x n m. n ≤ m ∧ x ∈ APPLYING w (X_WORLD_i n (Theta p) {A} {B} w) ⇒
       x ∈ APPLYING w (X_WORLD_i m (Theta p) {A} {B} w)
Proof
  rw[APPLYING_def] >>
  qexists_tac ‘γ’ >> gs[SUBSET_DEF] >> rw[] >>
  irule X_WORLD_i_grows >> qexists_tac ‘n’ >> gs[]
QED 

Theorem FINITE_APPLIED_SUBSET:
  ∀ γ. FINITE γ ⇒ (γ ⊆ APPLYING w (X_WORLD (Theta p) {A} {B} w) ⇔
                     ∃n. γ ⊆ APPLYING w (X_WORLD_i n (Theta p) {A} {B} w) 
                  )
Proof
  Induct_on ‘FINITE’ >> rw[EQ_IMP_THM] (* 3 *)
  >- (‘∃m. e ∈ APPLYING w (X_WORLD_i m (Theta p) {A} {B} w)’ by
        (gs[APPLYING_def] >> assume_tac FINITE_SUBSET_X_WORLD >>
         pop_assum $ qspec_then ‘set γ'’ strip_assume_tac >> gs[] >> 
         qexistsl_tac [‘n'’, ‘γ'’] >> gs[]
        ) >> gs[] >> 
      Cases_on ‘n ≤ m’
      >- (qexists_tac ‘m’ >> gs[SUBSET_DEF] >> rw[] >>
          last_x_assum $ qspec_then ‘x’ strip_assume_tac >> gs[] >> 
          metis_tac[APPLIED_X_WORLD_i_GROWS]
         )
      >- (‘m ≤ n’ by decide_tac >> qexists_tac ‘n’ >> rw[] >>
          metis_tac [APPLIED_X_WORLD_i_GROWS]
       ) 
     )
  >- (gs[X_WORLD_def, BIGUNION, PULL_EXISTS, APPLYING_def] >> qexists_tac ‘γ'’ >>
      gs[SUBSET_DEF] >> rw[] >> qexists_tac ‘n’ >> simp[]
     )
  >- (gs[X_WORLD_def, BIGUNION, PULL_EXISTS, APPLYING_def, SUBSET_DEF] >>
      rw[] >> first_x_assum $ qspec_then ‘x’ strip_assume_tac >> gs[] >>
      qexists_tac ‘γ''’ >> rw[] >> qexists_tac ‘n’ >> simp[]
     )   
QED
       
Theorem FINITE_EXISTS_LIST:
  ∀x. FINITE x ⇒ ∃l. set l = x 
Proof
  Induct_on ‘FINITE’ >>
  rw[] >> qexists_tac ‘e :: l’ >>
  gs[]
QED

Theorem FINITE_X_WORLD_i:
  ∀n θ a b w. FINITE (X_WORLD_i n θ {a} {b} w)
Proof
  Induct >> rw[X_WORLD_i_def]
QED

Theorem NOT_EMPTY_X_WORLD_i:
  ∀n θ a b w. X_WORLD_i n θ {a} {b} w ≠ ∅ 
Proof
  Induct >> rw[X_WORLD_i_def]
QED

Theorem APPLYING_TO_LARGER_SET:
  ∀ w x y p. p ∈ APPLYING w x ∧ x ⊆ y ⇒
             p ∈ APPLYING w y
Proof
  rw[APPLYING_def] >>
  metis_tac[SUBSET_DEF]
QED
              
Theorem APPLYING_TO_FINITE:
  ∀ w θ x γ p. FINITE x ∧ set γ = x ∧ S_Theory θ w ∧ p ∈ APPLYING w x ⇒
             CONJl γ --> p ∈ w
Proof
  rw[APPLYING_def] >>
  ‘R_Theory w’ by metis_tac [S_Theory_imp_R_Theory] >> gs[R_Theory_def, pENTAIL_def] >>
  last_assum irule >>
  qexists_tac ‘[CONJl γ' --> p]’ >> gs[CONJl_def] >>
  irule g_modus_ponens >> qexists_tac ‘CONJl γ --> CONJl γ'’ >>
  gs[g_suffixing] >> irule IMP_MEM_IMP_CONJl >>
  metis_tac[CONJl_MEM_IMP, SUBSET_DEF]
QED

Theorem Y_WORLD_i_grows:
  ∀ e n m Θ A R. e ∈ Y_WORLD_i n Θ A R ∧ n ≤ m ⇒
                   e ∈ Y_WORLD_i m Θ A R
Proof
  rpt strip_tac >> Induct_on ‘m’
  >- (rpt strip_tac >> gs[Y_WORLD_i_def])
  >> Cases_on ‘n = SUC m’ >> strip_tac
  >- gs[]
  >> ‘n ≤ m’ by decide_tac >> gs[Y_WORLD_i_def] >> rw[]
QED
        
Theorem FINITE_SUBSET_Y_WORLD:
    ∀s Θ A R. FINITE s ⇒ (s ⊆ Y_WORLD Θ A R ⇔ ∃n. s ⊆ Y_WORLD_i n Θ A R)
Proof
  Induct_on ‘FINITE’ >> simp[] >> 
  rpt strip_tac >> simp[Y_WORLD_def, PULL_EXISTS] >> reverse eq_tac
  >- metis_tac[]
  >> rpt strip_tac >>
  rename [‘e ∈ Y_WORLD_i m Θ I' R’,
          ‘s ⊆ Y_WORLD_i n Θ I' R’] >> 
  Cases_on ‘m ≤ n’
  >- metis_tac[Y_WORLD_i_grows]
  >> ‘n < m’ by decide_tac >>
  qexists_tac ‘m’ >> simp[SUBSET_DEF] >> rpt strip_tac >>
  irule Y_WORLD_i_grows >> qexists_tac ‘n’ >> gs[] >> 
  metis_tac[SUBSET_DEF]
QED

        
        
Theorem Completeness:
  (∀ (RF : (g_prop set) R_FRAME) VF. Holds RF VF RF.Z p) ⇒ |- p
Proof
  rw[] >> CCONTR_TAC >> 
  last_x_assum $ qspecl_then [‘(Canonical_Frame p)’,
                           ‘λ x. {w | g_VAR x ∈ w}’] strip_assume_tac >>
  ‘∀A w. w ∈ (Canonical_Frame p).W ⇒ 
      (Holds (Canonical_Frame p) (λx. {w | g_VAR x ∈ w}) w A ⇔ A ∈ w)’ by (* turn into different theorem *)
    (Induct_on ‘A’ >> gs[Holds_def] >> rw[](* 4 *)
     >- (reverse $ rw[EQ_IMP_THM] >> rename [‘A --> B ∈ w’]
         >- (qpat_x_assum ‘(Canonical_Frame p).R w x y’ mp_tac >>
             rw[Canonical_Frame_def, APPLYING_def, SUBSET_DEF, sENTAILS_def] >>
             last_x_assum irule >> qexists_tac ‘[A]’ >>
             gs[CONJl_def]
             )
         >- (CCONTR_TAC >>
             qpat_x_assum
             ‘∀x y.
                x ∈ (Canonical_Frame p).W ∧ y ∈ (Canonical_Frame p).W ∧
                (Canonical_Frame p).R w x y ∧
                Holds (Canonical_Frame p) (λx. {w | g_VAR x ∈ w}) x A ⇒
                B ∈ y’ mp_tac >> gs[] >>
             qexistsl_tac [‘X_WORLD (Theta p) {A} {B} w’,
                           ‘Y_WORLD (Theta p) (APPLYING w (X_WORLD (Theta p) {A} {B} w)) {B}’] >>
             ‘X_WORLD (Theta p) {A} {B} w ∈ (Canonical_Frame p).W’ by
               (simp[Canonical_Frame_def] >>
                ‘S_Theory (Theta p) (X_WORLD (Theta p) {A} {B} w)’ by
                  (rw[S_Theory_def, sENTAILS_def, Theta_Ordinary] >>
                   rename[‘CONJl γ --> D ∈ Theta p’] >>
                   simp[X_WORLD_def, PULL_EXISTS] >>
                   qexists_tac ‘SUC (R_gn D)’ >>
                   simp[X_WORLD_i_def] >>
                   ‘D = LINV R_gn 𝕌(:g_prop) (R_gn D)’ by (
                     ‘D ∈ 𝕌(:g_prop)’ by simp[] >>
                     ‘INJ R_gn 𝕌(:g_prop)  𝕌(:num)’ by simp[INJ_DEF] >>
                     metis_tac [LINV_DEF]
                     ) >> simp[] >> 
                   ‘¬sENTAILS (Theta p)
                    (APPLYING w
                     (X_WORLD_i (R_gn D) (Theta p) {A} {B} w ∪
                      {D})) B’ suffices_by
                        (‘APPLYING w
                          (X_WORLD_i (R_gn D) (Theta p) {A} {B} w ∪
                           {LINV R_gn 𝕌(:g_prop) (R_gn D)}) =
                          APPLYING w
                                   (X_WORLD_i (R_gn D) (Theta p) {A} {B} w ∪
                                    {D})’ by
                           (rw[EXTENSION, EQ_IMP_THM] >> metis_tac[]
                           ) >>
                         gs[]
                        ) >> 
                   CCONTR_TAC >> gs[sENTAILS_def] >>
                   rename [‘CONJl δ --> B ∈ Theta p’] >>
                   ‘CONJl δ ∈ APPLYING w
                    (X_WORLD_i (R_gn D) (Theta p) {A} {B} w ∪
                     {D})’ by
                     (gs[Canonical_Frame_def] >> irule CONJl_IN_APPLIED >> metis_tac[]
                     ) >>
                   ‘∃l. set l = X_WORLD_i (R_gn D) (Theta p) {A} {B} w’ by
                     (irule FINITE_EXISTS_LIST >> simp[FINITE_X_WORLD_i]
                     ) >>
                   ‘l ++ γ ≠ [] ∧ set (l ++ γ) ⊆ X_WORLD (Theta p) {A} {B} w ∧ CONJl (l ++ γ) --> D ∈ Theta p’ by
                     (rw[] (* 2 *)
                      >- (rw[X_WORLD_def, BIGUNION, SUBSET_DEF, PULL_EXISTS] >> metis_tac[])
                      >- (‘Ordinary (Theta p)’ by gs[Theta_Ordinary] >>
                          gs[Ordinary_def, Prime_def, R_Theory_def, pENTAIL_def] >>
                          last_x_assum irule >> qexists_tac ‘[CONJl γ --> D]’ >>
                          gs[CONJl_def] >>
                          irule g_modus_ponens >>
                          qexists_tac ‘(CONJl l & CONJl γ) --> CONJl γ’ >>
                          gs[g_conjunction_r] >>
                          irule g_modus_ponens >>
                          qexists_tac ‘CONJl (l ++ γ) --> (CONJl l & CONJl γ)’ >> rw[]
                          >- (‘l ≠ []’ by
                                (CCONTR_TAC >> 
                                 gs[NOT_EMPTY_X_WORLD_i]
                                ) >>
                              assume_tac CONJl_split_equiv >>
                              pop_assum $ qspecl_then [‘l’, ‘γ’] strip_assume_tac >> 
                              metis_tac [goldblatt_provable_rules, g_DIMP_def]
                             )
                          >- metis_tac[g_suffixing, g_permutation, g_modus_ponens]
                         )
                     ) >>
                    ‘(CONJl (l ⧺ γ) & D --> CONJl δ) ∈ w’ by
                     (‘CONJl l & D --> CONJl δ ∈ w’ by (
                       ‘CONJl (l ++ [D]) --> CONJl δ ∈ w’ suffices_by (
                         rw[] >> 
                         ‘R_Theory w’ by (gs[Canonical_Frame_def] >> metis_tac[S_Theory_imp_R_Theory]) >>
                         gs[R_Theory_def, pENTAIL_def] >> last_x_assum irule >>
                         qexists_tac ‘[CONJl (l ⧺ [D]) --> CONJl δ]’ >> gs[CONJl_def] >>
                         irule g_modus_ponens >> qexists_tac ‘CONJl l & CONJl [D] --> CONJl (l ⧺ [D])’ >> rw[]
                         >- (‘l ≠ []’ by
                               (CCONTR_TAC >> 
                                gs[NOT_EMPTY_X_WORLD_i]
                               ) >> gs[CONJl_split]
                            )
                         >- gs[CONJl_def, g_suffixing]
                         ) >>
                       irule APPLYING_TO_FINITE >> gs[PULL_EXISTS, Canonical_Frame_def] >>
                       metis_tac[]
                       ) >>
                      ‘R_Theory w’ by (gs[Canonical_Frame_def] >> metis_tac[S_Theory_imp_R_Theory]) >>
                      gs[R_Theory_def, pENTAIL_def] >> last_x_assum irule >>
                      qexists_tac ‘[CONJl l & D --> CONJl δ]’ >> gs[CONJl_def] >>
                      irule g_modus_ponens >> qexists_tac ‘(CONJl (l ⧺ γ) & D) --> CONJl l & D’ >>
                      gs[g_suffixing] >>
                      ‘l ≠ []’ by
                        (CCONTR_TAC >> 
                         gs[NOT_EMPTY_X_WORLD_i]
                        ) >>
                      ‘|- (CONJl (l ⧺ γ) --> CONJl l & CONJl γ)’ by metis_tac[CONJl_split] >>
                      metis_tac[goldblatt_provable_rules]
                     ) >> 
                   ‘(CONJl (l ++ γ) & D --> CONJl δ) --> CONJl (l ++ γ) --> CONJl δ ∈ Theta p’ by
                     (‘Ordinary (Theta p)’ by gs[Theta_Ordinary] >>
                      gs[Ordinary_def, Regular_def] >>
                      ‘CONJl (l ++ γ) --> CONJl (l ++ γ) ∈ Theta p’ by simp[g_identity] >>
                      ‘CONJl (l ++ γ) --> (CONJl (l ++ γ) & D) ∈ Theta p’ by
                        (gs[R_Theory_def, pENTAIL_def] >> last_x_assum irule >> 
                         qexists_tac ‘[CONJl (l ++ γ) --> CONJl (l ++ γ); CONJl (l ++ γ) --> D]’ >> 
                         gs[CONJl_def, g_conj_introduction] 
                        ) >> 
                      gs[R_Theory_def, pENTAIL_def] >> last_x_assum irule >>
                      qexists_tac ‘[CONJl (l ⧺ γ) --> CONJl (l ⧺ γ) & D]’ >>
                      gs[CONJl_def, g_suffixing]
                     ) >>
                   ‘CONJl (l ⧺ γ) --> CONJl δ ∈ w’ by 
                     (‘S_Theory (Theta p) w’ by gs[Canonical_Frame_def] >>
                      gs[S_Theory_def, sENTAILS_def] >> last_x_assum irule >>
                      qexists_tac ‘[CONJl (l ⧺ γ) & D --> CONJl δ]’ >>
                      gs[CONJl_def]
                     ) >>
                   ‘¬sENTAILS (Theta p) (APPLYING w (X_WORLD (Theta p) {A} {B} w)) B’ by
                     (rw[sENTAILS_def] >>
                      rename [‘α = [] ∨ ¬(set α ⊆ APPLYING w (X_WORLD (Theta p) {A} {B} w)) ∨
                               CONJl α --> B ∉ Theta p’] >>
                      Cases_on ‘α = []’ >> gs[] >> 
                      Cases_on ‘CONJl α --> B ∉ Theta p’ >> gs[] >>
                      assume_tac FINITE_APPLIED_SUBSET >> gs[] >>
                      Induct
                      >- (gs[X_WORLD_i_def] >> CCONTR_TAC >>
                          gs[] >>
                          ‘CONJl α ∈ APPLYING w {A}’ by
                            (gs[Canonical_Frame_def] >> irule CONJl_IN_APPLIED >>
                             metis_tac[]
                            ) >>
                          pop_assum mp_tac >> simp[APPLYING_def] >> CCONTR_TAC >> gs[] >>
                          qpat_x_assum ‘A --> B ∉ w’ mp_tac >> gs[Canonical_Frame_def, S_Theory_def] >>
                          last_x_assum irule >> simp[sENTAILS_def] >> qexists_tac ‘[CONJl γ' --> CONJl α]’ >>
                          simp[CONJl_def] >> gs[Ordinary_def, Prime_def, R_Theory_def, pENTAIL_def] >>
                          last_x_assum irule >>
                          qexists_tac ‘[CONJl α --> B]’ >> gs[CONJl_def] >>
                          metis_tac[g_modus_ponens, g_suffixing, g_permutation, g_A_CONJl_A]
                         )
                      >- (rw[X_WORLD_i_def] >>
                          CCONTR_TAC >>
                          qpat_x_assum
                          ‘¬sENTAILS (Theta p)
                           (APPLYING w
                            (X_WORLD_i n (Theta p) {A} {B} w ∪ {LINV R_gn 𝕌(:g_prop) n})) B’ mp_tac >> 
                          gs[] >> simp[sENTAILS_def] >> metis_tac[]
                         )
                    ) >>
                   pop_assum mp_tac >> rw[sENTAILS_def] >>
                   qexists_tac ‘[CONJl δ]’ >> rw[CONJl_def, APPLYING_def] >>
                   metis_tac[]
                  ) >> rw[] >>
                irule Maximal_S_Theory_APP_imp_prime >> rw[] (* 2 *)
                >- (gs[X_WORLD_def, EXTENSION, PULL_EXISTS] >>
                    qexistsl_tac [‘A’, ‘{A}’, ‘0’] >> gs[X_WORLD_i_def]
                   )
                >- (qexistsl_tac [‘B’, ‘w’, ‘Theta p’] >> gs[Canonical_Frame_def] >> rw[] (* 2 *)
                    >- (rw[sENTAILS_def] >> CCONTR_TAC >> 
                        qpat_x_assum ‘E ∉ X_WORLD (Theta p) {A} {B} w’ mp_tac >> rw[] >> 
                        assume_tac FINITE_SUBSET_X_WORLD >> 
                        pop_assum $ qspec_then ‘{E}’ strip_assume_tac >> gs[] >>
                        qexists_tac ‘SUC (R_gn E)’ >> gs[X_WORLD_i_def] >> 
                        ‘¬sENTAILS (Theta p)
                         (APPLYING w
                          (X_WORLD_i (R_gn E) (Theta p) {A} {B} w ∪
                           {LINV R_gn 𝕌(:g_prop) (R_gn E)})) B’ suffices_by
                          (rw[] >>
                           ‘E = LINV R_gn 𝕌(:g_prop) (R_gn E)’ by (
                             ‘E ∈ 𝕌(:g_prop)’ by simp[] >>
                             ‘INJ R_gn 𝕌(:g_prop)  𝕌(:num)’ by simp[INJ_DEF] >>
                             metis_tac [LINV_DEF]
                             ) >> gs[]
                          ) >> gs[sENTAILS_def] >> rw[] >>
                        ‘E = LINV R_gn 𝕌(:g_prop) (R_gn E)’ by (
                          ‘E ∈ 𝕌(:g_prop)’ by simp[] >>
                          ‘INJ R_gn 𝕌(:g_prop)  𝕌(:num)’ by simp[INJ_DEF] >>
                          metis_tac [LINV_DEF]
                          ) >>
                        Cases_on ‘γ = []’ >> simp[] >>
                        Cases_on ‘CONJl γ --> B ∈ Theta p’ >> gs[] >> CCONTR_TAC >>
                        first_x_assum $ qspec_then ‘γ’ mp_tac >> gs[SUBSET_DEF, APPLYING_def] >>
                        rw[] >> first_x_assum $ qspec_then ‘x’ strip_assume_tac >> gs[] >> 
                        qexists_tac ‘γ'’ >> rw[] >> first_x_assum $ qspec_then ‘x'’ strip_assume_tac >> 
                        gs[] >> assume_tac FINITE_SUBSET_X_WORLD >>
                        pop_assum $ qspec_then ‘{x'}’ strip_assume_tac >> gs[] >>
                        ‘∃n. x' ∈ X_WORLD_i n (Theta p) {A} {B} w’ suffices_by gs[] >>
                        metis_tac[]   
                       )
                    >- (rw[sENTAILS_def] >>
                        Cases_on ‘γ = []’ >> simp[] >> 
                        Cases_on ‘CONJl γ --> B ∈ Theta p’ >> simp[] >> 
                        assume_tac FINITE_APPLIED_SUBSET >>
                        pop_assum $ qspec_then ‘set γ’ strip_assume_tac >> 
                        gs[] >> rw[] >> Induct_on ‘n’
                        >- (CCONTR_TAC >> gs[] >>
                            ‘(A --> CONJl γ) --> A --> B ∈ Theta p’ by
                              (assume_tac Theta_Theta_theory >>
                               pop_assum $ qspec_then ‘p’ strip_assume_tac >>
                               gs[S_Theory_def, Ordinary_def, Regular_def, sENTAILS_def] >>
                               pop_assum irule >>
                               qexists_tac ‘[CONJl γ --> B]’ >> simp[CONJl_def] >> last_x_assum irule >>
                               metis_tac[g_suffixing, g_modus_ponens, g_permutation]
                              ) >> gs[X_WORLD_i_def] >> 
                            ‘A --> CONJl γ ∈ w’ by
                              (irule APPLYING_WORLDS >> 
                               gs[Canonical_Frame_def, Prime_def] >>
                               qexists_tac ‘Theta p’ >> gs[]
                              ) >> gs[Canonical_Frame_def, S_Theory_def, sENTAILS_def] >> 
                            qpat_x_assum ‘A --> B ∉ w’ mp_tac >> simp[] >>
                            last_x_assum irule >> qexists_tac ‘[A --> CONJl γ]’ >> gs[CONJl_def]
                           )
                        >- (rw[X_WORLD_i_def] >> gs[sENTAILS_def] >> 
                            last_x_assum $ qspec_then ‘γ’ strip_assume_tac
                           )
                       )
                   )
               ) >> 
             ‘Y_WORLD (Theta p) (APPLYING w (X_WORLD (Theta p) {A} {B} w)) {B} ∈ (Canonical_Frame p).W’ by
               (simp[Canonical_Frame_def] >> 
                ‘S_Theory (Theta p)
                 (Y_WORLD (Theta p) (APPLYING w (X_WORLD (Theta p) {A} {B} w)) {B})’ by
                  (rw[S_Theory_def, sENTAILS_def, Theta_Ordinary] >>
                   rename[‘CONJl γ --> D ∈ Theta p’] >>
                   simp[Y_WORLD_def, PULL_EXISTS] >>
                   qexists_tac ‘SUC (R_gn D)’ >>
                   simp[Y_WORLD_i_def] >>
                   ‘D = LINV R_gn 𝕌(:g_prop) (R_gn D)’ by (
                     ‘D ∈ 𝕌(:g_prop)’ by simp[] >>
                     ‘INJ R_gn 𝕌(:g_prop)  𝕌(:num)’ by simp[INJ_DEF] >>
                     metis_tac [LINV_DEF]
                     ) >> simp[] >>
                   ‘¬sENTAILS (Theta p)
                    (Y_WORLD_i (R_gn D) (Theta p)
                     (APPLYING w (X_WORLD (Theta p) {A} {B} w)) {B} ∪
                     {D}) B’ suffices_by
                     (‘Y_WORLD_i (R_gn D) (Theta p)
                       (APPLYING w (X_WORLD (Theta p) {A} {B} w)) {B} ∪
                       {LINV R_gn 𝕌(:g_prop) (R_gn D)} = Y_WORLD_i (R_gn D) (Theta p)
                                       (APPLYING w (X_WORLD (Theta p) {A} {B} w)) {B} ∪
                                       {D}’ by
                        (rw[EXTENSION, EQ_IMP_THM] >> metis_tac[]
                        ) >>
                      gs[]
                     ) >>
                   CCONTR_TAC >> gs[sENTAILS_def] >>
                   rename [‘CONJl δ --> B ∈ Theta p’] >>
                 ‘¬sENTAILS (Theta p) (Y_WORLD (Theta p) (APPLYING w (X_WORLD (Theta p) {A} {B} w)) {B}) B’ by
                     (rw[sENTAILS_def] >>
                      rename [‘α = [] ∨
                               ¬(set α ⊆
                                 Y_WORLD (Theta p) (APPLYING w (X_WORLD (Theta p) {A} {B} w)) {B}) ∨
                               CONJl α --> B ∉ Theta p’] >>
                      Cases_on ‘α = []’ >> simp[] >> 
                      Cases_on ‘CONJl α --> B ∈ Theta p’ >> simp[] >> 
                      assume_tac FINITE_SUBSET_Y_WORLD >>
                      pop_assum $ qspec_then ‘set α’ strip_assume_tac >> 
                      gs[] >> rw[] >> Induct_on ‘n’ (* 2 *)
                      >- (gs[Y_WORLD_i_def] >>
                          assume_tac FINITE_APPLIED_SUBSET >>
                          pop_assum $ qspec_then ‘set α’ strip_assume_tac >> gs[] >>
                          Induct  (* 2 *)
                          >- (CCONTR_TAC >> gs[] >>
                              ‘(A --> CONJl α) --> A --> B ∈ Theta p’ by
                                (assume_tac Theta_Theta_theory >>
                                 pop_assum $ qspec_then ‘p’ strip_assume_tac >>
                                 gs[S_Theory_def, Ordinary_def, Regular_def, sENTAILS_def] >>
                                 pop_assum irule >>
                                 qexists_tac ‘[CONJl α --> B]’ >> simp[CONJl_def] >> last_x_assum irule >>
                                 metis_tac[g_suffixing, g_modus_ponens, g_permutation]
                                ) >> gs[X_WORLD_i_def] >> 
                              ‘A --> CONJl α ∈ w’ by
                                (irule APPLYING_WORLDS >> 
                                 gs[Canonical_Frame_def, Prime_def] >>
                                 qexists_tac ‘Theta p’ >> gs[]
                                ) >> gs[Canonical_Frame_def, S_Theory_def, sENTAILS_def] >> 
                              qpat_x_assum ‘A --> B ∉ w’ mp_tac >> simp[] >>
                              last_x_assum irule >> qexists_tac ‘[A --> CONJl α]’ >> gs[CONJl_def]
                             )
                          >- (rw[X_WORLD_i_def] >> gs[sENTAILS_def] >> 
                              last_x_assum $ qspec_then ‘α’ strip_assume_tac
                             )
                         )
                      >- (rw[Y_WORLD_i_def] >> gs[sENTAILS_def] >> 
                          last_x_assum $ qspec_then ‘α’ strip_assume_tac
                         )
                     ) >> pop_assum mp_tac >> simp[sENTAILS_def] >>
                  qexists_tac ‘γ ++ FILTER (λx. x ≠ D) δ’ >> rw[] (* 2 *)
                   >- (gs[SUBSET_DEF] >> rw[] >>
                       first_x_assum $ qspec_then ‘x’ strip_assume_tac >>
                       ‘MEM x δ’ by metis_tac[MEM_FILTER_LEMMA] >>
                       gs[] (* 2 *)
                       >- (assume_tac FINITE_SUBSET_Y_WORLD >>
                           pop_assum $ qspecl_then [‘{x}’, ‘Theta p’, ‘APPLYING w (X_WORLD (Theta p) {A} {B} w)’,
                                                    ‘{B}’] strip_assume_tac >>
                           gs[SUBSET_DEF] >> metis_tac[]
                          )
                       >- gs[NOT_MEM_FILTER_LEMMA]
                      )
                   >- (‘S_Theory (Theta p) (Theta p)’ by gs[Theta_Theta_theory] >>
                       gs[S_Theory_def, sENTAILS_def] >> last_assum irule >>
                       qexists_tac ‘[CONJl δ --> B]’ >> gs[CONJl_def] >>
                       last_assum irule >> qexists_tac ‘[CONJl γ & CONJl δ --> CONJl δ]’ >>
                       rw[CONJl_def]
                       >- gs[g_conjunction_r, Ordinary_def, Regular_def]
                       >- (last_assum irule >>
                           qexists_tac ‘[CONJl (γ ++ δ) --> CONJl γ & CONJl δ]’ >> rw[CONJl_def]
                           >- gs[CONJl_split, Ordinary_def, Regular_def]
                           >- (last_assum irule >> qexists_tac ‘[CONJl (γ ⧺ FILTER (λx. x ≠ D) δ) --> CONJl (γ ⧺ δ)]’ >> 
                               reverse $ rw[CONJl_def]
                               >- (gs[Ordinary_def, Regular_def] >> qpat_x_assum ‘∀p'. |- p' ⇒ p' ∈ Theta p’ irule >>
                                   metis_tac[g_suffixing, g_permutation, g_modus_ponens]
                                  )
                               >- (last_assum irule >> qexists_tac ‘[CONJl γ & CONJl δ --> CONJl (γ ++ δ)]’ >>
                                   rw[CONJl_def]
                                   >- gs[CONJl_split, Ordinary_def, Regular_def] 
                                   >-  (last_assum irule >> 
                                        qexists_tac ‘[CONJl (γ ⧺ FILTER (λx. x ≠ D) δ) --> CONJl γ & CONJl δ]’ >>
                                        reverse $ rw[CONJl_def]
                                        >- gs[g_suffixing, Ordinary_def, Regular_def]
                                        >- (Cases_on ‘FILTER (λx. x ≠ D) δ = []’  >> gs[]
                                            >- (last_assum irule >> 
                                                qexists_tac ‘[CONJl γ --> CONJl γ; CONJl γ --> CONJl δ]’ >>
                                                gs[g_conj_introduction, CONJl_def, Ordinary_def, Regular_def, g_identity, R_Theory_def] >>
                                                qpat_x_assum ‘ ∀p'. Theta p |-^ p' ⇒ p' ∈ Theta p’ irule >> 
                                                gs[pENTAIL_def] >> qexists_tac ‘[CONJl γ --> D]’ >> gs[CONJl_def] >>
                                                ‘set δ ⊆ {D}’ by gs[EMPTY_FILTER_LEMMA] >> 
                                                metis_tac[goldblatt_provable_rules, g_A_CONJl_A, g_permutation]
                                               )
                                            >- (‘R_Theory (Theta p)’ by gs[Theta_R_Theory] >>
                                                gs[R_Theory_def] >> qpat_assum ‘∀p'. Theta p |-^ p' ⇒ p' ∈ Theta p’ irule >>
                                                simp[pENTAIL_def] >> 
                                                qexists_tac ‘[CONJl (γ ⧺ FILTER (λx. x ≠ D) δ) -->
                                                              (CONJl γ & CONJl (FILTER (λx. x ≠ D) δ) & D)]’ >>
                                                reverse $ rw[CONJl_def]
                                                >- (irule g_modus_ponens >>
                                                    qexists_tac ‘CONJl γ & CONJl (FILTER (λx. x ≠ D) δ) & D --> CONJl γ & CONJl δ’ >>
                                                    reverse $ rw[]
                                                    >- metis_tac[g_suffixing, g_permutation, g_modus_ponens]
                                                    >- (‘|- (CONJl (FILTER (λx. x ≠ D) δ) & D --> CONJl δ)’ by 
                                                          (Cases_on ‘MEM D δ’
                                                           >- metis_tac[FILTER_AND_FILTERED_IMP_CONJl, goldblatt_provable_rules]
                                                           >- metis_tac[goldblatt_provable_rules, FILTER_NON_MEM_EQUAL]
                                                          ) >> 
                                                        ‘|- (CONJl γ & CONJl (FILTER (λx. x ≠ D) δ) & D --> CONJl δ)’ by
                                                          (‘|- (CONJl γ & (CONJl (FILTER (λx. x ≠ D) δ) & D) --> CONJl δ)’ by
                                                             metis_tac[goldblatt_provable_rules, g_AND_STRENGTHEN] >>
                                                           metis_tac[g_suffixing, g_modus_ponens, g_AND_associative_rl]
                                                          ) >>
                                                        metis_tac[goldblatt_provable_rules]
                                                       )
                                                   )
                                                >- (qpat_assum ‘∀p'. Theta p |-^ p' ⇒ p' ∈ Theta p’ irule >>
                                                    simp[pENTAIL_def] >>
                                                    qexists_tac ‘[CONJl (γ ⧺ FILTER (λx. x ≠ D) δ) --> CONJl γ & CONJl (FILTER (λx. x ≠ D) δ);
                                                                  CONJl (γ ⧺ FILTER (λx. x ≠ D) δ) --> D]’ >>
                                                    rw[CONJl_def] (* 3 *)
                                                    >- (gs[Ordinary_def, Regular_def] >> gs[CONJl_split]
                                                       )
                                                    >- (pop_assum irule >> gs[pENTAIL_def] >>
                                                        qexists_tac ‘[CONJl γ --> D]’ >> gs[CONJl_def] >> irule g_modus_ponens >>
                                                        qexists_tac ‘CONJl γ & CONJl (FILTER (λx. x ≠ D) δ) --> CONJl γ’ >> gs[g_conjunction_l] >>
                                                        irule g_modus_ponens >>
                                                        qexists_tac ‘CONJl (γ ⧺ FILTER (λx. x ≠ D) δ) -->
                                                                     CONJl γ & CONJl (FILTER (λx. x ≠ D) δ)’ >> gs[CONJl_split] >> 
                                                        metis_tac[g_suffixing, g_modus_ponens, g_permutation]
                                                       )
                                                    >- gs[g_conj_introduction]
                                                   )
                                               )
                                           )
                                       )
                                  )
                              )
                          )
                      )
                  ) >> 
                simp[] >>
                Cases_on ‘Y_WORLD (Theta p) (APPLYING w (X_WORLD (Theta p) {A} {B} w)) {B} = ∅’
                >- gs[Prime_def, R_Theory_def, pENTAIL_def]
                >> irule Maximal_S_Theory_imp_prime >>
                simp[] >>
                qexistsl_tac [‘B’, ‘Theta p’] >> rw[] (* 2 *)
                >- (rw[sENTAILS_def] >> CCONTR_TAC >> 
                    qpat_x_assum ‘E ∉ Y_WORLD (Theta p)
                                  (APPLYING w (X_WORLD (Theta p) {A} {B} w)) {B}’ mp_tac >> rw[] >> 
                    assume_tac FINITE_SUBSET_Y_WORLD >>
                    pop_assum $ qspec_then ‘{E}’ strip_assume_tac >> gs[] >>
                    qexists_tac ‘SUC (R_gn E)’ >> gs[Y_WORLD_i_def] >> 
                    ‘E = LINV R_gn 𝕌(:g_prop) (R_gn E)’ by (
                      ‘E ∈ 𝕌(:g_prop)’ by simp[] >>
                      ‘INJ R_gn 𝕌(:g_prop)  𝕌(:num)’ by simp[INJ_DEF] >>
                      metis_tac [LINV_DEF]
                      ) >>
                    ‘¬sENTAILS (Theta p)
                     (Y_WORLD_i (R_gn E) (Theta p)
                      (APPLYING w (X_WORLD (Theta p) {A} {B} w)) {B} ∪
                      {LINV R_gn 𝕌(:g_prop) (R_gn E)}) B’ suffices_by gs[] >>
                    gs[sENTAILS_def] >> rw[] >> 
                    Cases_on ‘γ = []’ >> simp[] >>
                    Cases_on ‘CONJl γ --> B ∈ Theta p’ >> gs[] >> CCONTR_TAC >>
                    first_x_assum $ qspec_then ‘γ’ mp_tac >>
                    gs[SUBSET_DEF] >> rw[] >> first_x_assum $ qspec_then ‘x’ strip_assume_tac >>
                    gs[] >> assume_tac FINITE_SUBSET_Y_WORLD >>
                    pop_assum $ qspec_then ‘{x}’ strip_assume_tac >> gs[] >>
                    metis_tac[]
                   )
                >- (rw[sENTAILS_def] >>
                    Cases_on ‘γ = []’ >> simp[] >> 
                    Cases_on ‘CONJl γ --> B ∈ Theta p’ >> simp[] >> 
                    assume_tac FINITE_SUBSET_Y_WORLD >>
                    pop_assum $ qspec_then ‘set γ’ strip_assume_tac >> 
                    gs[] >> rw[] >> Induct_on ‘n’ (* 2 *)
                    >- (gs[Y_WORLD_i_def] >>
                        assume_tac FINITE_APPLIED_SUBSET >>
                        pop_assum $ qspec_then ‘set γ’ strip_assume_tac >> gs[] >>
                        Induct  (* 2 *)
                        >- (CCONTR_TAC >> gs[] >>
                            ‘(A --> CONJl γ) --> A --> B ∈ Theta p’ by
                              (assume_tac Theta_Theta_theory >>
                               pop_assum $ qspec_then ‘p’ strip_assume_tac >>
                               gs[S_Theory_def, Ordinary_def, Regular_def, sENTAILS_def] >>
                               pop_assum irule >>
                               qexists_tac ‘[CONJl γ --> B]’ >> simp[CONJl_def] >> last_x_assum irule >>
                               metis_tac[g_suffixing, g_modus_ponens, g_permutation]
                              ) >> gs[X_WORLD_i_def] >> 
                            ‘A --> CONJl γ ∈ w’ by
                              (irule APPLYING_WORLDS >> 
                               gs[Canonical_Frame_def, Prime_def] >>
                               qexists_tac ‘Theta p’ >> gs[]
                              ) >> gs[Canonical_Frame_def, S_Theory_def, sENTAILS_def] >> 
                            qpat_x_assum ‘A --> B ∉ w’ mp_tac >> simp[] >>
                            last_x_assum irule >> qexists_tac ‘[A --> CONJl γ]’ >> gs[CONJl_def]
                           )
                        >- (rw[X_WORLD_i_def] >> gs[sENTAILS_def] >> 
                            last_x_assum $ qspec_then ‘γ’ strip_assume_tac
                           )
                       )
                    >- (rw[Y_WORLD_i_def] >> gs[sENTAILS_def] >> 
                        last_x_assum $ qspec_then ‘γ’ strip_assume_tac
                       )
                   )
               ) >> 
             gs[] >> rw[] (* 3 *)
             >- (gs[Canonical_Frame_def] >>
                 rw[Y_WORLD_def, BIGUNION, SUBSET_DEF, PULL_EXISTS] >>
                 qexists_tac ‘0’ >> gs[Y_WORLD_i_def]
                )
             >- (rw[X_WORLD_def, BIGUNION, PULL_EXISTS] >>
                 qexists_tac ‘0’ >> gs[X_WORLD_i_def]
                )
             >- (rw[Y_WORLD_def] >> CCONTR_TAC >> gs[] >>
                 qpat_x_assum
                 ‘B ∈ Y_WORLD_i n (Theta p) (APPLYING w (X_WORLD (Theta p) {A} {B} w)) {B}’ mp_tac >>
                 simp[] >> Induct_on ‘n’ >> rw[Y_WORLD_i_def] (* 3 *)
                 >- (simp[APPLYING_def] >> CCONTR_TAC >> gs[] >>
                     pop_assum mp_tac >> assume_tac FINITE_SUBSET_X_WORLD >>
                     pop_assum $ qspec_then ‘set γ’ strip_assume_tac >> gs[] >>
                     Induct_on ‘n’ >> rw[X_WORLD_i_def]
                     >- (CCONTR_TAC >> gs[] >>
                         qpat_x_assum ‘A --> B ∉ w’ mp_tac >> simp[] >>
                         qpat_x_assum ‘w ∈ (Canonical_Frame p).W’ mp_tac >>
                         rw[Canonical_Frame_def, Prime_def, R_Theory_def] >>
                         last_x_assum irule >> simp[pENTAIL_def] >>
                         qexists_tac ‘[CONJl γ --> B]’ >> simp[CONJl_def] >>
                         irule g_modus_ponens >> qexists_tac ‘A --> CONJl γ’ >>
                         simp[g_suffixing, g_A_CONJl_A]
                        )
                     >- (CCONTR_TAC >> gs[] >>
                         qpat_x_assum
                         ‘¬sENTAILS (Theta p)
                          (APPLYING w
                           (X_WORLD_i n (Theta p) {A} {B} w ∪ {LINV R_gn 𝕌(:g_prop) n})) B’
                         mp_tac >> simp[sENTAILS_def] >> qexists_tac ‘[B]’ >>
                         gs[APPLYING_def, CONJl_def] >> rw[] (* 2 *)
                         >- (qexists_tac ‘γ’ >> gs[])
                         >- (‘Ordinary (Theta p)’ by gs[Theta_Ordinary] >>
                             gs[Ordinary_def, Regular_def, g_identity]
                            )
                        )
                    )
                 >- (CCONTR_TAC >>
                     qpat_x_assum
                     ‘¬sENTAILS (Theta p)
                      (Y_WORLD_i n (Theta p) (APPLYING w (X_WORLD (Theta p) {A} {B} w))
                       {B} ∪ {LINV R_gn 𝕌(:g_prop) n}) B’ mp_tac >>
                     gs[sENTAILS_def] >> qexists_tac ‘[B]’ >> 
                     gs[CONJl_def] >> ‘Ordinary (Theta p)’ by gs[Theta_Ordinary] >>
                     gs[Ordinary_def, Regular_def, g_identity]
                  )
                 >- (CCONTR_TAC >>
                     qpat_x_assum
                     ‘¬sENTAILS (Theta p)
                      (Y_WORLD_i n (Theta p) (APPLYING w (X_WORLD (Theta p) {A} {B} w))
                       {B} ∪ {LINV R_gn 𝕌(:g_prop) n}) B’ mp_tac >>
                     gs[] >> rename[‘B = B'’] >>
                     simp[sENTAILS_def] >> qexists_tac ‘[B']’ >>
                     gs[CONJl_def] >> ‘Ordinary (Theta p)’ by gs[Theta_Ordinary] >>
                     gs[Ordinary_def, Regular_def, g_identity]
                    )
                )
            )
        ) 
     >- (rw[EQ_IMP_THM] >> rename[‘A & B ∈ w’] >> 
         qpat_x_assum ‘w ∈ (Canonical_Frame p).W’ mp_tac >> 
         simp[Canonical_Frame_def, S_Theory_def, sENTAILS_def] >> rw[]  (* 3 *)
         >- (last_x_assum irule >> qexists_tac ‘[A; B]’ >>
             gs[CONJl_def, Ordinary_def, Regular_def, g_identity]
            )
         >- (last_x_assum irule >> 
             qexists_tac ‘[A & B]’ >>
             gs[CONJl_def, Ordinary_def, Regular_def, g_conjunction_l]
            )
         >- (last_x_assum irule >> 
             qexists_tac ‘[A & B]’ >>
             gs[CONJl_def, Ordinary_def, Regular_def, g_conjunction_r]
            )
        )
     >- (‘(Canonical_Frame p).STAR w ∈ (Canonical_Frame p).W’ by
           (‘Reduced_R_Frame (Canonical_Frame p)’ by 
              (assume_tac Canonical_Frame_is_R_Frame >>
               pop_assum $ qspec_then ‘p’ strip_assume_tac >> gs[]
              ) >> gs[R_STAR_CLOSURE]
           ) >> rw[EQ_IMP_THM] >> gs[Canonical_Frame_def]
        )
     >- (rw[EQ_IMP_THM] (* 2 *)
         >- (pop_assum mp_tac >> simp[Canonical_Frame_def] >> rw[] >>
             gs[SUBSET_DEF, APPLYING_def] >> last_x_assum irule >>
             qexists_tac ‘[τ]’ >>
             gs[CONJl_def, g_identity, S_Theory_def, Ordinary_def, Regular_def] >>
             qpat_x_assum ‘∀p'. |- p' ⇒ p' ∈ Theta p’ irule >> 
             metis_tac[goldblatt_provable_rules]
            )
         >- (‘(Canonical_Frame p).R w (Canonical_Frame p).Z w’ by
               (‘Reduced_R_Frame (Canonical_Frame p)’ by 
                  (assume_tac Canonical_Frame_is_R_Frame >>
                   pop_assum $ qspec_then ‘p’ strip_assume_tac >> gs[]
                  ) >>
                ‘(Canonical_Frame p).R (Canonical_Frame p).Z w w’ by
                  gs[R_R_ZERO_REFLEX] >>
                gs[R_R_COMM]
               ) >> 
             simp[Canonical_Frame_def] >>
             assume_tac Theta_Ordinary >> pop_assum $ qspec_then ‘p’ strip_assume_tac >> gs[Ordinary_def] >>
             assume_tac Theta_Theta_theory >> pop_assum $ qspec_then ‘p’ strip_assume_tac >> 
             gs[Canonical_Frame_def] >>
             qpat_x_assum ‘APPLYING w (Theta p) ⊆ w’ mp_tac >> rw[APPLYING_def,SUBSET_DEF] >>
             last_x_assum irule >> qexists_tac ‘[x]’ >> rw[CONJl_def] (* 2 *)
             >- (gs[S_Theory_def] >> last_x_assum irule >>
                 simp[sENTAILS_def] >> qexists_tac ‘[τ]’ >> gs[CONJl_def, Regular_def] >>
                 qpat_x_assum ‘∀p'. |- p' ⇒ p' ∈ Theta p’ irule >>
                 metis_tac[goldblatt_provable_rules]
                )
             >- (gs[S_Theory_def] >> last_x_assum irule >> simp[sENTAILS_def] >>
                 qexists_tac ‘γ’ >> gs[SUBSET_DEF]
                )
            )
        )
    ) >>
  last_x_assum $ qspecl_then [‘p’, ‘(Canonical_Frame p).Z’] strip_assume_tac >> 
  ‘Ordinary (Theta p)’ by gs[Theta_Ordinary] >> 
  gs[Canonical_Frame_def, Theta_Theta_theory, Ordinary_def] >> qpat_x_assum ‘p ∈ Theta p’ mp_tac >> 
  assume_tac Theta_Maximal_Rejection >> gs[Maximal_Excluding_def] >>
  pop_assum $ qspec_then ‘p’ strip_assume_tac >> gs[] >>
  CCONTR_TAC >> qpat_x_assum ‘¬(Theta p |-^ p)’ mp_tac >> simp[pENTAIL_def] >>
  gs[] >> qexists_tac ‘[p]’ >> gs[CONJl_def, g_identity]
QED
        
val _ = export_theory();

