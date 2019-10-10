(* ------------- Var midamble.v --------------- *)
Instance Name_NamedThing_TyCoVar : Name.NamedThing TyCoVar.
intros r d. eapply d. eapply Name.NamedThing__Dict_Build.
eapply varName. intro v. eapply Name.nameOccName. eapply varName. exact v.
Qed.
Instance Name_NamedThing_VarId : Name.NamedThing Id.
intros r d. eapply d. eapply Name.NamedThing__Dict_Build.
eapply varName. intro v. eapply Name.nameOccName. eapply varName. exact v.
Qed.


