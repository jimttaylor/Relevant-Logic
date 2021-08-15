




open HolKernel Parse boolLib bossLib stringTheory;

val _ = new_theory "RelevantLogic";


    
Datatype: prop = Var string
          | Imp prop prop
                
End

val _ = set_fixity "-->" (Infixr 490);
val _ = overload_on ("-->", “Imp”);

Inductive provable:
[identity:] (∀(A:prop). provable (A --> A)) ∧
[permutation:] (∀A B C. provable ((A --> (B --> C)) --> (B --> (A --> C)))) ∧
[transitivity:] (∀A B C. provable ((A --> B) --> ((B --> C) --> (A --> C)))) ∧
[contraction:] (∀A B. provable ((A --> (A --> B)) --> (A --> B))) ∧
[modus_ponens:] (∀A B. provable A ∧ provable (A --> B) ⇒ provable B)
End

Theorem assertion:
  ∀A B. provable (A --> ((A --> B) --> B))
Proof
  rpt strip_tac >> irule modus_ponens >> qexists_tac ‘(A --> B) --> (A --> B)’ >>
  simp [identity, permutation]
QED

Theorem prefixing:
  ∀A B C. provable ((A --> B) --> ((C --> A) --> (C --> B)))
Proof
  metis_tac[provable_rules]
QED

Theorem affixing:
  ∀A B C D. provable (A --> B) ∧ provable (C --> D) ⇒ provable ((B --> C) --> (A --> D))
Proof
  metis_tac[provable_rules]
QED

(*TODO: Slaney ⇔ Goldblatt*)
       
val _ = export_theory();

