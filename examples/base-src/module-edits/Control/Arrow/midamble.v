(* Specialization of Control.Arrow.first and Control.Arrow.second to the (->) type 
   constructor. 

   Coq often has difficulty with type inference for the Arrow type class. One work 
   around is to add the following to your edit file:
     rename value Control.Arrow.first  = Control.Arrow.arrow_first
     rename value Control.Arrow.second = Control.Arrow.arrow_second

*)

Definition arrow_first {b}{c}{d} (f : (b -> c)) : (b * d)%type -> (c * d)%type :=
  fun p => match p with (x,y)=> (f x, y) end.
Definition arrow_second {b}{c}{d} (f : (b -> c)) : (d * b)%type -> (d * c)%type :=
  fun p => match p with (x,y)=> (x, f y) end.
