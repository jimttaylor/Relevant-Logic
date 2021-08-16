




open HolKernel Parse boolLib bossLib stringTheory;

val _ = new_theory "RelevantLogic";


    
Datatype: prop = Var string
          | IMP prop prop
          | AND prop prop
          | OR prop prop
          | NOT prop
          | tt
End
        
val _ = set_fixity "-->" (Infixr 490);
val _ = overload_on ("-->", “IMP”);

val _ = set_fixity "&" (Infixr 490);
val _ = overload_on ("&", “AND”);

val _ = set_fixity "V" (Infixr 490);
val _ = overload_on ("V", “OR”);

val _ = overload_on ("~", “NOT”);


Definition DIMP:
  DIMP A B = (A --> B) & (B --> A)
End
    
val _ = set_fixity "<->" (Infixr 490);
val _ = overload_on ("<->", “DIMP”);

Definition ICONJ:
  ICONJ A B = ~(A --> ~B)
End

val _ = set_fixity "io" (Infixr 490);
val _ = overload_on ("io", “ICONJ”);

                
Inductive slaney_provable: 
[s_identity:] (∀(A:prop). slaney_provable (A --> A)) ∧
[s_permutation:] (∀A B C. slaney_provable ((A --> (B --> C)) --> (B --> (A --> C)))) ∧
[s_transitivity:] (∀A B C. slaney_provable ((A --> B) --> ((B --> C) --> (A --> C)))) ∧
[s_contraction:] (∀A B. slaney_provable ((A --> (A --> B)) --> (A --> B))) ∧
[s_conjunction_l:] (∀A B. slaney_provable ((A & B) --> A)) ∧ 
[s_conjunction_r:] (∀A B. slaney_provable ((A & B) --> B)) ∧ 
[s_conj_introduction:] (∀A B C. slaney_provable (((A --> B) & (A --> C)) --> (A --> (B & C)))) ∧
[s_disjunction_l:] (∀A B. slaney_provable (A --> (A V B))) ∧
[s_disjunction_r:] (∀A B. slaney_provable (A --> (A V B))) ∧
[s_disjunction_elim:] (∀A B C. slaney_provable (((A --> C) & (B --> C)) --> ((A V B) --> C))) ∧
[s_distribution:] (∀A B C. slaney_provable ((A & (B V C)) --> ((A & B) V (A & C)))) ∧
[s_contrapositive:] (∀A B. slaney_provable ((A --> (~B)) --> (B --> (~A)))) ∧ 
[s_double_negation:] (∀A. slaney_provable ((~(~A)) --> A )) ∧
[s_adjunction_rule:] (∀A B. slaney_provable A ∧ slaney_provable B ⇒ slaney_provable (A --> B)) ∧ 
[s_modus_ponens:] (∀A B. slaney_provable A ∧ slaney_provable (A --> B) ⇒ slaney_provable B)
End


Theorem s_assertion:
  ∀A B. slaney_provable (A --> ((A --> B) --> B))
Proof
  rpt strip_tac >> irule s_modus_ponens >> qexists_tac ‘(A --> B) --> (A --> B)’ >>
  simp [s_identity, s_permutation]
QED

Theorem s_prefixing:
  ∀A B C. slaney_provable ((A --> B) --> ((C --> A) --> (C --> B)))
Proof
  metis_tac[slaney_provable_rules]
QED

Theorem s_affixing:
  ∀A B C D. slaney_provable (A --> B) ∧ slaney_provable (C --> D) ⇒ slaney_provable ((B --> C) --> (A --> D))
Proof
  metis_tac[slaney_provable_rules]
QED

Inductive goldblatt_provable: 
[g_identity:] (∀(A:prop). goldblatt_provable (A --> A)) ∧
[g_suffixing:] (∀ A B C. goldblatt_provable ((A --> B) --> ((B --> C) --> (A --> C)))) ∧
[g_assertion:]  (∀A B. goldblatt_provable (A --> ((A --> B) --> B))) ∧
[g_contraction:] (∀A B. goldblatt_provable ((A --> (A --> B)) --> (A --> B))) ∧
[g_conjunction_l:] (∀A B. goldblatt_provable((A & B) --> A)) ∧ 
[g_conjunction_r:] (∀A B. goldblatt_provable ((A & B) --> B)) ∧ 
[g_conj_introduction:] (∀A B C. goldblatt_provable (((A --> B) & (A --> C)) --> (A --> (B & C)))) ∧
[g_disjunction_l:] (∀A B. goldblatt_provable (A --> (A V B))) ∧
[g_disjunction_r:] (∀A B. goldblatt_provable (A --> (A V B))) ∧
[g_disjunction_elim:] (∀A B C. goldblatt_provable (((A --> C) & (B --> C)) --> ((A V B) --> C))) ∧
[g_distribution:] (∀A B C. goldblatt_provable ((A & (B V C)) --> ((A & B) V (A & C)))) ∧
[g_contrapositive:] (∀A B. goldblatt_provable ((A --> (~B)) --> (B --> (~A)))) ∧ 
[g_double_negation:] (∀A. goldblatt_provable ((~(~A)) --> A )) ∧
[g_adjunction_rule:] (∀A B. goldblatt_provable A ∧ goldblatt_provable B ⇒ goldblatt_provable (A & B)) ∧ 
[g_modus_ponens:] (∀A B. goldblatt_provable A ∧ goldblatt_provable (A --> B) ⇒ goldblatt_provable B)
End

Theorem goldblatt_implies_slaney:
  ∀A. goldblatt_provable A ⇒ slaney_provable A
Proof
  Induct_on ‘goldblatt_provable A’ >> metis_tac[slaney_provable_rules]
QED

(* TODO: find a proof of this *)
Theorem g_permutation:
  ∀A B C. goldblatt_provable ((A --> (B --> C)) --> (B --> (A --> C)))
Proof
  metis_tac[g_suffixing, g_assertion, g_modus_ponens]
QED        

Theorem slaney_implies_goldblatt:
  ∀A. slaney_provable A ⇒ goldblatt_provable A
Proof
  Induct_on ‘slaney_provable A’ >> metis_tac[goldblatt_provable_rules, g_permutation]
QED

Theorem goldblatt_iff_slaney:
  ∀A. goldblatt_provable A ⇔ slaney_provable A
Proof
  metis_tac[slaney_implies_goldblatt, goldblatt_implies_slaney]
QED
        
        
Theorem g_prefixing: 
  ∀A B C. goldblatt_provable ((A --> B) --> ((C --> A) --> (C --> B)))
Proof
  metis_tac[goldblatt_provable_rules]
QED

Theorem g_double_negation_I:
  ∀A. goldblatt_provable (A --> ~~A)
Proof
  metis_tac[goldblatt_provable_rules]
QED

(* this is long, maybe consider proving it manually *)
Theorem g_reductio:
  ∀A. goldblatt_provable ((A --> ~A) --> ~A)
Proof
  metis_tac[goldblatt_provable_rules]
QED


(* figure out how to have <-> version *)

Theorem s_demorgan_1:
  ∀A B. slaney_provable (~(A V B) --> (~A) & (~B))
Proof
  metis_tac[slaney_provable_rules]
        

                
val _ = export_theory();

    
