(* Record selector *)
Require Import Pair.

(* Notation for Alt *)
(* Definition Alt b := prod (prod Core.AltCon (list b)) (Core.Expr b). *)

(* Redefinition with correct recursion structure *)
Require OrdList.

Definition stripTicksE {b} (p : Core.Tickish Core.Var -> bool) (expr : Core.Expr b) : Core.Expr b :=
  let go := fix  go arg__ := match arg__ with
              | Core.App e a        => Core.App (go e) (go a)
              | Core.Lam b e        => Core.Lam b (go e)
              | Core.Let b e        => Core.Let (go_bs b) (go e)
              | Core.Case e b t as_ => let fix map_go_a arg__ := match arg__ with
                                             | nil              => nil
                                             | cons (c,bs,e) xs => cons (c, bs, go e) (map_go_a xs)
                                           end
                                       in Core.Case (go e) b t (map_go_a as_)
              | Core.Cast e c       => Core.Cast (go e) c
              | Core.Tick t e       => if p t
                                       then go e
                                       else Core.Tick t (go e)
              | other               => other
            end
            with go_bs arg__ := match arg__ with
              | Core.NonRec b e => Core.NonRec b (go e)
              | Core.Rec bs     => let fix map_go_b arg__ := match arg__ with
                                         | nil           => nil
                                         | cons (b,e) xs => cons (b, go e) xs
                                       end
                                   in Core.Rec (map_go_b bs)
            end
            for go
  in go expr.

Definition stripTicksT {b} (p : Core.Tickish Core.Var -> bool) (expr : Core.Expr b) : list (Core.Tickish Core.Var) :=
  let go := fix  go arg__ := match arg__ with
              | Core.App e a        => OrdList.appOL (go e) (go a)
              | Core.Lam _ e        => go e
              | Core.Let b e        => OrdList.appOL (go_bs b) (go e)
              | Core.Case e _ _ as_ => let fix map_go_a arg__ := match arg__ with
                                             | nil              => nil
                                             | cons (_,_,e) xs => cons (go e) (map_go_a xs)
                                           end
                                       in OrdList.appOL (go e) (OrdList.concatOL (map_go_a as_))
              | Core.Cast e _       => go e
              | Core.Tick t e       => if p t
                                       then OrdList.consOL t (go e)
                                       else go e
              | _                   => OrdList.nilOL
            end
            with go_bs arg__ := match arg__ with
              | Core.NonRec _ e => go e
              | Core.Rec bs     => let fix map_go_b arg__ := match arg__ with
                                         | nil           => nil
                                         | cons (_,e) xs => cons (go e) (map_go_b xs)
                                       end
                                   in OrdList.concatOL (map_go_b bs)
            end
            for go
  in OrdList.fromOL (go expr).
