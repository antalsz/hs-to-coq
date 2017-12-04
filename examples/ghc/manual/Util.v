(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require Coq.Init.Datatypes.
Require Coq.Lists.List.
Require Data.Bits.
Require Data.Data.
Require Data.Either.
Require Data.Foldable.
Require Data.IORef.
Require Data.IntMap.Base.
Require Data.OldList.
Require Data.Ord.
Require Data.Set.Base.
Require Data.Time.Clock.UTC.
Require Data.Traversable.
Require Data.Tuple.
Require Exception.
Require GHC.Base.
Require GHC.Char.
Require GHC.Exts.
Require GHC.IO.Encoding.
Require GHC.IO.Exception.
Require GHC.IO.Handle.
Require GHC.IO.Handle.Types.
Require GHC.IO.Unsafe.
Require GHC.IORef.
Require GHC.List.
Require GHC.Num.
Require GHC.Prim.
Require GHC.Read.
Require GHC.Real.
Require System.Directory.
Require System.FilePath.Posix.
Require System.IO.Error.
Require Text.ParserCombinators.ReadP.
Require Text.Read.
Import Data.Bits.Notations.
Import GHC.Base.Notations.
Import GHC.Num.Notations.
Import GHC.Real.Notations.
Import System.FilePath.Posix.Notations.

(* Converted type declarations: *)

Definition Suffix :=
  GHC.Base.String%type.

Inductive Direction : Type := Forwards : Direction
                           |  Backwards : Direction.
(* Converted value declarations: *)

(* The Haskell code containes partial or untranslateable code, which needs the
   following *)

Axiom missingValue : forall {a}, a.

Axiom patternFailure : forall {a}, a.

Definition abstractConstr : GHC.Base.String -> Data.Data.Constr :=
  fun n =>
    Data.Data.mkConstr (abstractDataType n) (Coq.Init.Datatypes.app
                                            (GHC.Base.hs_string__ "{abstract:") (Coq.Init.Datatypes.app n
                                                                                                        (GHC.Base.hs_string__
                                                                                                        "}"))) nil
    Data.Data.Prefix.

Definition abstractDataType : GHC.Base.String -> Data.Data.DataType :=
  fun n => Data.Data.mkDataType n (cons (abstractConstr n) nil).

Definition all2 {a} {b} : (a -> b -> bool) -> list a -> list b -> bool :=
  fix all2 arg_295__ arg_296__ arg_297__
        := match arg_295__ , arg_296__ , arg_297__ with
             | _ , nil , nil => true
             | p , cons x xs , cons y ys => andb (p x y) (all2 p xs ys)
             | _ , _ , _ => false
           end.

Definition atLength {a} {b} : (list a -> b) -> b -> list
                              a -> GHC.Num.Int -> b :=
  fun atLenPred atEnd ls n =>
    let go :=
      fix go arg_345__ arg_346__
            := let j_349__ :=
                 match arg_345__ , arg_346__ with
                   | _ , nil => atEnd
                   | n , cons _ xs => go (n GHC.Num.- GHC.Num.fromInteger 1) xs
                 end in
               match arg_345__ , arg_346__ with
                 | num_347__ , ls => if num_347__ GHC.Base.== GHC.Num.fromInteger 0 : bool
                                     then atLenPred ls
                                     else j_349__
               end in
    let j_352__ := go n ls in
    if n GHC.Base.< GHC.Num.fromInteger 0 : bool
    then atLenPred ls
    else j_352__.

Definition lengthAtLeast {a} : list a -> GHC.Num.Int -> bool :=
  atLength (GHC.Base.const true) false.

Definition lengthIs {a} : list a -> GHC.Num.Int -> bool :=
  atLength Data.Foldable.null false.

Definition listLengthCmp {a} : list a -> GHC.Num.Int -> comparison :=
  let atLen := fun arg_357__ => match arg_357__ with | nil => Eq | _ => Gt end in
  let atEnd := Lt in atLength atLen atEnd.

Definition charToC : GHC.Word.Word8 -> GHC.Base.String :=
  fun w =>
    let scrut_7__ := GHC.Char.chr (GHC.Real.fromIntegral w) in
    match scrut_7__ with
      | (""""%char) => GHC.Base.hs_string__ "\"""
      | ("'"%char) => GHC.Base.hs_string__ "\'"
      | ("\"%char) => GHC.Base.hs_string__ "\\"
      | c => let j_11__ :=
               cons (GHC.Char.hs_char__ "\") (cons (GHC.Char.chr (GHC.Char.ord
                                                                 (GHC.Char.hs_char__ "0") GHC.Num.+ GHC.Real.div
                                                                 (GHC.Char.ord c) (GHC.Num.fromInteger 64))) (cons
                                                   (GHC.Char.chr (GHC.Char.ord (GHC.Char.hs_char__ "0") GHC.Num.+
                                                                 GHC.Real.mod_ (GHC.Real.div (GHC.Char.ord c)
                                                                                             (GHC.Num.fromInteger 8))
                                                                               (GHC.Num.fromInteger 8))) (cons
                                                   (GHC.Char.chr (GHC.Char.ord (GHC.Char.hs_char__ "0") GHC.Num.+
                                                                 GHC.Real.mod_ (GHC.Char.ord c) (GHC.Num.fromInteger
                                                                               8))) nil))) in
             if andb (c GHC.Base.>= GHC.Char.hs_char__ " ") (c GHC.Base.<= GHC.Char.hs_char__
                     "~") : bool
             then cons c nil
             else j_11__
    end.

Definition chkAppend {a} : list a -> list a -> list a :=
  fun xs ys =>
    let j_447__ := Coq.Init.Datatypes.app xs ys in
    if Data.Foldable.null ys : bool
    then xs
    else j_447__.

Definition chunkList {a} : GHC.Num.Int -> list a -> list (list a) :=
  fix chunkList arg_319__ arg_320__
        := match arg_319__ , arg_320__ with
             | _ , nil => nil
             | n , xs => match GHC.List.splitAt n xs with
                           | pair as_ bs => cons as_ (chunkList n bs)
                         end
           end.

Definition cmpList {a} : (a -> a -> comparison) -> list a -> list
                         a -> comparison :=
  fix cmpList arg_216__ arg_217__ arg_218__
        := match arg_216__ , arg_217__ , arg_218__ with
             | _ , nil , nil => Eq
             | _ , nil , _ => Lt
             | _ , _ , nil => Gt
             | cmp , cons a as_ , cons b bs => let scrut_219__ := cmp a b in
                                               match scrut_219__ with
                                                 | Eq => cmpList cmp as_ bs
                                                 | xxx => xxx
                                               end
           end.

Definition compareLength {a} {b} : list a -> list b -> comparison :=
  fix compareLength arg_334__ arg_335__
        := match arg_334__ , arg_335__ with
             | nil , nil => Eq
             | cons _ xs , cons _ ys => compareLength xs ys
             | nil , _ => Lt
             | _ , nil => Gt
           end.

Definition leLength {a} {b} : list a -> list b -> bool :=
  fun xs ys =>
    let scrut_338__ := compareLength xs ys in
    match scrut_338__ with
      | Lt => true
      | Eq => true
      | Gt => false
    end.

Definition consIORef {a} : GHC.IORef.IORef (list a) -> a -> GHC.Types.IO unit :=
  fun var x => Data.IORef.atomicModifyIORef' var (fun xs => pair (cons x xs) tt).

Definition count {a} : (a -> bool) -> list a -> GHC.Num.Int :=
  fix count arg_289__ arg_290__
        := match arg_289__ , arg_290__ with
             | _ , nil => GHC.Num.fromInteger 0
             | p , cons x xs => let j_292__ := count p xs in
                                if p x : bool
                                then GHC.Num.fromInteger 1 GHC.Num.+ count p xs
                                else j_292__
           end.

Definition debugIsOn : bool :=
  false.

Definition minWith {b} {a} `{GHC.Base.Ord b} : (a -> b) -> list a -> a :=
  fun get_key xs =>
    if andb debugIsOn (negb (negb (Data.Foldable.null xs))) : bool
    then (Panic.assertPanic (GHC.Base.hs_string__ "ghc/compiler/utils/Util.hs")
         (GHC.Num.fromInteger 559))
    else GHC.List.head (GHC.Exts.sortWith get_key xs).

Definition doesDirNameExist : GHC.Base.String -> GHC.Types.IO bool :=
  fun fpath =>
    System.Directory.doesDirectoryExist (System.FilePath.Posix.takeDirectory fpath).

Definition dropList {b} {a} : list b -> list a -> list a :=
  fix dropList arg_279__ arg_280__
        := match arg_279__ , arg_280__ with
             | nil , xs => xs
             | _ , (nil as xs) => xs
             | cons _ xs , cons _ ys => dropList xs ys
           end.

Definition dropTail {a} : GHC.Num.Int -> list a -> list a :=
  fun n xs =>
    let go :=
      fix go arg_267__ arg_268__
            := match arg_267__ , arg_268__ with
                 | cons _ ys , cons x xs => cons x (go ys xs)
                 | _ , _ => nil
               end in
    go (GHC.List.drop n xs) xs.

Definition dropWhileEndLE {a} : (a -> bool) -> list a -> list a :=
  fun p =>
    Data.Foldable.foldr (fun x r =>
                          if andb (Data.Foldable.null r) (p x) : bool
                          then nil
                          else cons x r) nil.

Definition removeSpaces : GHC.Base.String -> GHC.Base.String :=
  dropWhileEndLE GHC.Unicode.isSpace GHC.Base.∘ GHC.List.dropWhile
  GHC.Unicode.isSpace.

Definition eqListBy {a} : (a -> a -> bool) -> list a -> list a -> bool :=
  fix eqListBy arg_229__ arg_230__ arg_231__
        := match arg_229__ , arg_230__ , arg_231__ with
             | _ , nil , nil => true
             | eq , cons x xs , cons y ys => andb (eq x y) (eqListBy eq xs ys)
             | _ , _ , _ => false
           end.

Definition eqMaybeBy {a} : (a -> a -> bool) -> option a -> option a -> bool :=
  fun arg_224__ arg_225__ arg_226__ =>
    match arg_224__ , arg_225__ , arg_226__ with
      | _ , None , None => true
      | eq , Some x , Some y => eq x y
      | _ , _ , _ => false
    end.

Definition equalLength {a} {b} : list a -> list b -> bool :=
  fix equalLength arg_341__ arg_342__
        := match arg_341__ , arg_342__ with
             | nil , nil => true
             | cons _ xs , cons _ ys => equalLength xs ys
             | _ , _ => false
           end.

Definition escapeSpaces : GHC.Base.String -> GHC.Base.String :=
  Data.Foldable.foldr (fun c s =>
                        if GHC.Unicode.isSpace c : bool
                        then cons (GHC.Char.hs_char__ "\") (cons c s)
                        else cons c s) (GHC.Base.hs_string__ "").

Definition filterByList {a} : list bool -> list a -> list a :=
  fix filterByList arg_423__ arg_424__
        := match arg_423__ , arg_424__ with
             | cons true bs , cons x xs => cons x (filterByList bs xs)
             | cons false bs , cons _ xs => filterByList bs xs
             | _ , _ => nil
           end.

Definition filterByLists {a} : list bool -> list a -> list a -> list a :=
  fix filterByLists arg_417__ arg_418__ arg_419__
        := match arg_417__ , arg_418__ , arg_419__ with
             | cons true bs , cons x xs , cons _ ys => cons x (filterByLists bs xs ys)
             | cons false bs , cons _ xs , cons y ys => cons y (filterByLists bs xs ys)
             | _ , _ , _ => nil
           end.

Definition filterOut {a} : (a -> bool) -> list a -> list a :=
  fix filterOut arg_467__ arg_468__
        := match arg_467__ , arg_468__ with
             | _ , nil => nil
             | p , cons x xs => let j_469__ := cons x (filterOut p xs) in
                                if p x : bool
                                then filterOut p xs
                                else j_469__
           end.

Definition first3M {m} {a} {d} {b} {c} `{GHC.Base.Monad m} : (a -> m d) -> (a *
                                                             b * c)%type -> m (d * b * c)%type :=
  fun arg_472__ arg_473__ =>
    match arg_472__ , arg_473__ with
      | f , pair (pair x y) z => GHC.Base.liftM (fun x' => pair (pair x' y) z) (f x)
    end.

Definition firstM {m} {a} {c} {b} `{GHC.Base.Monad m} : (a -> m c) -> (a *
                                                        b)%type -> m (c * b)%type :=
  fun arg_477__ arg_478__ =>
    match arg_477__ , arg_478__ with
      | f , pair x y => GHC.Base.liftM (fun x' => pair x' y) (f x)
    end.

Definition foldl2 {acc} {a} {b} : (acc -> a -> b -> acc) -> acc -> list
                                  a -> list b -> acc :=
  fix foldl2 arg_300__ arg_301__ arg_302__ arg_303__
        := match arg_300__ , arg_301__ , arg_302__ , arg_303__ with
             | _ , z , nil , nil => z
             | k , z , cons a as_ , cons b bs => foldl2 k (k z a b) as_ bs
             | _ , _ , _ , _ => Panic.panic (GHC.Base.hs_string__ "Util: foldl2")
           end.

Definition fst3 {a} {d} {b} {c} : (a -> d) -> (a * b * c)%type -> (d * b *
                                  c)%type :=
  fun arg_502__ arg_503__ =>
    match arg_502__ , arg_503__ with
      | f , pair (pair a b) c => pair (pair (f a) b) c
    end.

Definition fstOf3 {a} {b} {c} : (a * b * c)%type -> a :=
  fun arg_510__ => match arg_510__ with | pair (pair a _) _ => a end.

Definition getCmd : GHC.Base.String -> Data.Either.Either GHC.Base.String
                    (GHC.Base.String * GHC.Base.String)%type :=
  fun s =>
    let scrut_104__ :=
      GHC.List.break GHC.Unicode.isSpace GHC.Base.$ GHC.List.dropWhile
      GHC.Unicode.isSpace s in
    match scrut_104__ with
      | pair nil _ => Data.Either.Left (Coq.Init.Datatypes.app (GHC.Base.hs_string__
                                                               "Couldn't find command in ") (GHC.Show.show s))
      | res => Data.Either.Right res
    end.

Definition getModificationUTCTime : GHC.Base.String -> GHC.Types.IO
                                    Data.Time.Clock.UTC.UTCTime :=
  System.Directory.getModificationTime.

Definition modificationTimeIfExists : GHC.Base.String -> GHC.Types.IO (option
                                                                      Data.Time.Clock.UTC.UTCTime) :=
  fun f =>
    Exception.catchIO (getModificationUTCTime f GHC.Base.>>= (fun t =>
                        GHC.Base.return_ (Some t))) (fun e =>
                        if System.IO.Error.isDoesNotExistError e : bool
                        then GHC.Base.return_ None
                        else GHC.IO.Exception.ioError e).

Definition ghciSupported : bool :=
  false.

Definition ghciTablesNextToCode : bool :=
  false.

Definition global {a} : a -> GHC.IORef.IORef a :=
  fun a => GHC.IO.Unsafe.unsafePerformIO (GHC.IORef.newIORef a).

Definition globalM {a} : GHC.Types.IO a -> GHC.IORef.IORef a :=
  fun ma => GHC.IO.Unsafe.unsafePerformIO (ma GHC.Base.>>= GHC.IORef.newIORef).

Definition golden : GHC.Int.Int32 :=
  GHC.Num.fromInteger 1013904242.

Definition hSetTranslit : GHC.IO.Handle.Types.Handle -> GHC.Types.IO unit :=
  fun h =>
    GHC.IO.Handle.hGetEncoding h GHC.Base.>>= (fun menc =>
      let scrut_42__ := GHC.Base.fmap textEncodingName menc in
      let j_44__ := GHC.Base.return_ tt in
      match scrut_42__ with
        | Some name => if Data.Foldable.notElem (GHC.Char.hs_char__ "/") name : bool
                       then (GHC.IO.Encoding.mkTextEncoding GHC.Base.$ Coq.Init.Datatypes.app name
                                                                                              (GHC.Base.hs_string__
                                                                                              "//TRANSLIT"))
                            GHC.Base.>>= (fun enc' => GHC.IO.Handle.hSetEncoding h enc')
                       else j_44__
        | _ => j_44__
      end).

Definition isDarwinHost : bool :=
  true.

Definition isEqual : comparison -> bool :=
  fun arg_237__ =>
    match arg_237__ with
      | Gt => false
      | Eq => true
      | Lt => false
    end.

Definition isIn {a} `{GHC.Base.Eq_ a} : GHC.Base.String -> a -> list
                                        a -> bool :=
  fun _msg x ys => Data.Foldable.elem x ys.

Definition isSingleton {a} : list a -> bool :=
  fun arg_331__ => match arg_331__ with | cons _ nil => true | _ => false end.

Definition isWindowsHost : bool :=
  false.

Definition isn'tIn {a} `{GHC.Base.Eq_ a} : GHC.Base.String -> a -> list
                                           a -> bool :=
  fun _msg x ys => Data.Foldable.notElem x ys.

Definition liftFst {a} {b} {c} : (a -> b) -> (a * c)%type -> (b * c)%type :=
  fun arg_486__ arg_487__ =>
    match arg_486__ , arg_487__ with
      | f , pair a c => pair (f a) c
    end.

Definition liftSnd {a} {b} {c} : (a -> b) -> (c * a)%type -> (c * b)%type :=
  fun arg_482__ arg_483__ =>
    match arg_482__ , arg_483__ with
      | f , pair c a => pair c (f a)
    end.

Definition looksLikeModuleName : GHC.Base.String -> bool :=
  fix looksLikeModuleName arg_109__
        := match arg_109__ with
             | nil => false
             | cons c cs => let go :=
                              fix go arg_110__
                                    := match arg_110__ with
                                         | nil => true
                                         | cons ("."%char) cs => looksLikeModuleName cs
                                         | cons c cs => andb (orb (GHC.Unicode.isAlphaNum c) (orb (c GHC.Base.==
                                                                                                  GHC.Char.hs_char__
                                                                                                  "_") (c GHC.Base.==
                                                                                                  GHC.Char.hs_char__
                                                                                                  "'"))) (go cs)
                                       end in
                            andb (GHC.Unicode.isUpper c) (go cs)
           end.

Definition makeRelativeTo
    : GHC.Base.String -> GHC.Base.String -> GHC.Base.String :=
  fun this that =>
    let f :=
      fix f arg_17__ arg_18__
            := let j_20__ :=
                 match arg_17__ , arg_18__ with
                   | xs , ys => Coq.Init.Datatypes.app (GHC.List.replicate (Data.Foldable.length
                                                                           ys) (GHC.Base.hs_string__ "..")) xs
                 end in
               match arg_17__ , arg_18__ with
                 | cons x xs , cons y ys => if x GHC.Base.== y : bool
                                            then f xs ys
                                            else j_20__
                 | _ , _ => j_20__
               end in
    let thatDirectory := System.FilePath.Posix.dropFileName that in
    match System.FilePath.Posix.splitFileName this with
      | pair thisDirectory thisFilename => let directory :=
                                             System.FilePath.Posix.joinPath GHC.Base.$ f
                                             (System.FilePath.Posix.splitPath thisDirectory)
                                             (System.FilePath.Posix.splitPath thatDirectory) in
                                           directory System.FilePath.Posix.</> thisFilename
    end.

Definition mapAccumL2 {s1} {s2} {a} {b} : (s1 -> s2 -> a -> (s1 * s2 *
                                          b)%type) -> s1 -> s2 -> list a -> (s1 * s2 * list b)%type :=
  fun f s1 s2 xs =>
    match Data.Traversable.mapAccumL (fun arg_361__ arg_362__ =>
                                       match arg_361__ , arg_362__ with
                                         | pair s1 s2 , x => let scrut_363__ := f s1 s2 x in
                                                             match scrut_363__ with
                                                               | pair (pair s1' s2') y => pair (pair s1' s2') y
                                                             end
                                       end) (pair s1 s2) xs with
      | pair (pair s1' s2') ys => pair (pair s1' s2') ys
    end.

Definition mapAndUnzip {a} {b} {c} : (a -> (b * c)%type) -> list a -> (list b *
                                     list c)%type :=
  fix mapAndUnzip arg_385__ arg_386__
        := match arg_385__ , arg_386__ with
             | _ , nil => pair nil nil
             | f , cons x xs => match mapAndUnzip f xs with
                                  | pair rs1 rs2 => match f x with
                                                      | pair r1 r2 => pair (cons r1 rs1) (cons r2 rs2)
                                                    end
                                end
           end.

Definition mapAndUnzip3 {a} {b} {c} {d} : (a -> (b * c * d)%type) -> list
                                          a -> (list b * list c * list d)%type :=
  fix mapAndUnzip3 arg_378__ arg_379__
        := match arg_378__ , arg_379__ with
             | _ , nil => pair (pair nil nil) nil
             | f , cons x xs => match mapAndUnzip3 f xs with
                                  | pair (pair rs1 rs2) rs3 => match f x with
                                                                 | pair (pair r1 r2) r3 => pair (pair (cons r1 rs1)
                                                                                                      (cons r2 rs2))
                                                                                                (cons r3 rs3)
                                                               end
                                end
           end.

Definition mapFst {a} {c} {b} : (a -> c) -> list (a * b)%type -> list (c *
                                                                      b)%type :=
  fun f xys =>
    let cont_395__ arg_396__ :=
      match arg_396__ with
        | pair x y => cons (pair (f x) y) nil
      end in
    Coq.Lists.List.flat_map cont_395__ xys.

Definition mapSnd {b} {c} {a} : (b -> c) -> list (a * b)%type -> list (a *
                                                                      c)%type :=
  fun f xys =>
    let cont_392__ arg_393__ :=
      match arg_393__ with
        | pair x y => cons (pair x (f y)) nil
      end in
    Coq.Lists.List.flat_map cont_392__ xys.

Definition matchVectors {bv} `{Data.Bits.Bits bv} `{GHC.Num.Num bv}
    : GHC.Base.String -> Data.IntMap.Base.IntMap bv :=
  let go :=
    fun arg_128__ arg_129__ =>
      match arg_128__ , arg_129__ with
        | pair ix im , char => let im' :=
                                 Data.IntMap.Base.insertWith _Data.Bits..|._ (GHC.Char.ord char)
                                 (GHC.Num.fromInteger 2 GHC.Real.^ ix) im in
                               let ix' := ix GHC.Num.+ GHC.Num.fromInteger 1 in
                               GHC.Prim.seq ix' GHC.Base.$ (GHC.Prim.seq im' GHC.Base.$ pair ix' im')
      end in
  Data.Tuple.snd GHC.Base.∘ Data.Foldable.foldl' go (pair (GHC.Num.fromInteger
                                                          0 : GHC.Num.Int) Data.IntMap.Base.empty).

Definition maybeRead {a} `{GHC.Read.Read a} : GHC.Base.String -> option a :=
  fun str =>
    let scrut_55__ := Text.Read.reads str in
    match scrut_55__ with
      | cons (pair x "") nil => Some x
      | _ => None
    end.

Definition maybeReadFuzzy {a} `{GHC.Read.Read a} : GHC.Base.String -> option
                                                   a :=
  fun str =>
    let scrut_51__ := Text.Read.reads str in
    match scrut_51__ with
      | cons (pair x s) nil => if Data.Foldable.all GHC.Unicode.isSpace s : bool
                               then Some x
                               else None
      | _ => None
    end.

Definition mulHi : GHC.Int.Int32 -> GHC.Int.Int32 -> GHC.Int.Int32 :=
  fun a b =>
    let r : GHC.Int.Int64 :=
      GHC.Real.fromIntegral a GHC.Num.* GHC.Real.fromIntegral b in
    GHC.Real.fromIntegral (Data.Bits.shiftR r (GHC.Num.fromInteger 32)).

Definition hashInt32 : GHC.Int.Int32 -> GHC.Int.Int32 :=
  fun x => mulHi x golden GHC.Num.+ x.

Definition hashString : GHC.Base.String -> GHC.Int.Int32 :=
  let magic :=
    GHC.Real.fromIntegral (GHC.Num.fromInteger 3735928559 : GHC.Word.Word32) in
  let f :=
    fun m c =>
      (GHC.Real.fromIntegral (GHC.Char.ord c) GHC.Num.* magic) GHC.Num.+ hashInt32
      m in
  Data.Foldable.foldl' f golden.

Definition nOfThem {a} : GHC.Num.Int -> a -> list a :=
  fun n thing => GHC.List.replicate n thing.

Definition nTimes {a} : GHC.Num.Int -> (a -> a) -> (a -> a) :=
  fix nTimes arg_512__ arg_513__
        := let j_517__ :=
             match arg_512__ , arg_513__ with
               | n , f => f GHC.Base.∘ nTimes (n GHC.Num.- GHC.Num.fromInteger 1) f
             end in
           let j_519__ :=
             match arg_512__ , arg_513__ with
               | num_515__ , f => if num_515__ GHC.Base.== GHC.Num.fromInteger 1 : bool
                                  then f
                                  else j_517__
             end in
           match arg_512__ , arg_513__ with
             | num_514__ , _ => if num_514__ GHC.Base.== GHC.Num.fromInteger 0 : bool
                                then GHC.Base.id
                                else j_519__
           end.

Definition ncgDebugIsOn : bool :=
  false.

Definition notNull {a} : list a -> bool :=
  fun arg_329__ => match arg_329__ with | nil => false | _ => true end.

Definition lengthExceeds {a} : list a -> GHC.Num.Int -> bool :=
  atLength notNull false.

Definition nubSort {a} `{GHC.Base.Ord a} : list a -> list a :=
  Data.Set.Base.toAscList GHC.Base.∘ Data.Set.Base.fromList.

Definition only {a} : list a -> a :=
  fun arg_326__ =>
    match arg_326__ with
      | cons a _ => a
      | _ => Panic.panic (GHC.Base.hs_string__ "Util: only")
    end.

Definition op_zlzazazg__ {f} `{GHC.Base.Applicative f} : f bool -> f bool -> f
                                                         bool :=
  GHC.Base.liftA2 andb.

Notation "'_<&&>_'" := (op_zlzazazg__).

Infix "<&&>" := (_<&&>_) (at level 99).

Definition op_zlzbzbzg__ {f} `{GHC.Base.Applicative f} : f bool -> f bool -> f
                                                         bool :=
  GHC.Base.liftA2 orb.

Notation "'_<||>_'" := (op_zlzbzbzg__).

Infix "<||>" := (_<||>_) (at level 99).

Definition toArgs : GHC.Base.String -> Data.Either.Either GHC.Base.String (list
                                                                          GHC.Base.String) :=
  fun str =>
    let readAsString : GHC.Base.String -> Data.Either.Either GHC.Base.String
                       (GHC.Base.String * GHC.Base.String)%type :=
      fun s =>
        let scrut_172__ := Text.Read.reads s in
        let j_174__ :=
          Data.Either.Left (Coq.Init.Datatypes.app (GHC.Base.hs_string__ "Couldn't read ")
                                                   (Coq.Init.Datatypes.app (GHC.Show.show s) (GHC.Base.hs_string__
                                                                           " as String"))) in
        match scrut_172__ with
          | cons (pair arg rest) nil => if Data.Foldable.all GHC.Unicode.isSpace
                                           (GHC.List.take (GHC.Num.fromInteger 1) rest) : bool
                                        then Data.Either.Right (pair arg rest)
                                        else j_174__
          | _ => j_174__
        end in
    let toArgs' : GHC.Base.String -> Data.Either.Either GHC.Base.String (list
                                                                        GHC.Base.String) :=
      fix toArgs' s
            := let scrut_178__ := GHC.List.dropWhile GHC.Unicode.isSpace s in
               match scrut_178__ with
                 | nil => Data.Either.Right nil
                 | cons (""""%char) _ => let cont_180__ arg_181__ :=
                                           match arg_181__ with
                                             | pair arg rest => GHC.Base.fmap (fun arg_182__ => cons arg arg_182__)
                                                                              (toArgs' rest)
                                           end in
                                         readAsString s GHC.Base.>>= cont_180__
                 | s' => let scrut_185__ :=
                           GHC.List.break (GHC.Unicode.isSpace <||> (fun arg_184__ =>
                                            arg_184__ GHC.Base.== GHC.Char.hs_char__ """")) s' in
                         match scrut_185__ with
                           | pair argPart1 (cons (""""%char) _ as s'') => let cont_186__ arg_187__ :=
                                                                            match arg_187__ with
                                                                              | pair argPart2 rest => GHC.Base.fmap
                                                                                                      (fun arg_188__ =>
                                                                                                        cons
                                                                                                        (Coq.Init.Datatypes.app
                                                                                                        argPart1
                                                                                                        (GHC.Show.show
                                                                                                        argPart2))
                                                                                                        arg_188__)
                                                                                                      (toArgs' rest)
                                                                            end in
                                                                          readAsString s'' GHC.Base.>>= cont_186__
                           | pair arg s'' => GHC.Base.fmap (fun arg_190__ => cons arg arg_190__) (toArgs'
                                                           s'')
                         end
               end in
    let scrut_196__ := GHC.List.dropWhile GHC.Unicode.isSpace str in
    match scrut_196__ with
      | (cons ("["%char) _ as s) => let scrut_197__ := Text.Read.reads s in
                                    let j_199__ :=
                                      Data.Either.Left (Coq.Init.Datatypes.app (GHC.Base.hs_string__ "Couldn't read ")
                                                                               (Coq.Init.Datatypes.app (GHC.Show.show
                                                                                                       str)
                                                                                                       (GHC.Base.hs_string__
                                                                                                       " as [String]"))) in
                                    match scrut_197__ with
                                      | cons (pair args spaces) nil => if Data.Foldable.all GHC.Unicode.isSpace
                                                                          spaces : bool
                                                                       then Data.Either.Right args
                                                                       else j_199__
                                      | _ => j_199__
                                    end
      | s => toArgs' s
    end.

Definition toCmdArgs : GHC.Base.String -> Data.Either.Either GHC.Base.String
                       (GHC.Base.String * list GHC.Base.String)%type :=
  fun s =>
    let scrut_206__ := getCmd s in
    match scrut_206__ with
      | Data.Either.Left err => Data.Either.Left err
      | Data.Either.Right (pair cmd s') => let scrut_208__ := toArgs s' in
                                           match scrut_208__ with
                                             | Data.Either.Left err => Data.Either.Left err
                                             | Data.Either.Right args => Data.Either.Right (pair cmd args)
                                           end
    end.

Definition partitionByList {a} : list bool -> list a -> (list a * list
                                 a)%type :=
  let go :=
    fix go arg_408__ arg_409__ arg_410__ arg_411__
          := match arg_408__ , arg_409__ , arg_410__ , arg_411__ with
               | trues , falses , cons true bs , cons x xs => go (cons x trues) falses bs xs
               | trues , falses , cons false bs , cons x xs => go trues (cons x falses) bs xs
               | trues , falses , _ , _ => pair (GHC.List.reverse trues) (GHC.List.reverse
                                                falses)
             end in
  go nil nil.

Definition partitionWith {a} {b} {c} : (a -> Data.Either.Either b c) -> list
                                       a -> (list b * list c)%type :=
  fix partitionWith arg_457__ arg_458__
        := match arg_457__ , arg_458__ with
             | _ , nil => pair nil nil
             | f , cons x xs => match partitionWith f xs with
                                  | pair bs cs => let scrut_461__ := f x in
                                                  match scrut_461__ with
                                                    | Data.Either.Left b => pair (cons b bs) cs
                                                    | Data.Either.Right c => pair bs (cons c cs)
                                                  end
                                end
           end.

Definition readRational__ : Text.ParserCombinators.ReadP.ReadS
                            GHC.Real.Rational :=
  fun r =>
    let nonnull :=
      fun p s =>
        let cont_59__ arg_60__ :=
          match arg_60__ with
            | pair (cons _ _ as cs) t => GHC.Base.return_ (pair cs t)
            | _ => missingValue (GHC.Base.hs_string__
                                "Partial pattern match in `do' notation")
          end in
        GHC.Base.return_ (GHC.List.span p s) GHC.Base.>>= cont_59__ in
    let lexDotDigits :=
      fun arg_62__ =>
        match arg_62__ with
          | cons ("."%char) s => GHC.Base.return_ (GHC.List.span GHC.Unicode.isDigit s)
          | s => GHC.Base.return_ (pair (GHC.Base.hs_string__ "") s)
        end in
    let lexDecDigits := nonnull GHC.Unicode.isDigit in
    let readDec :=
      fun s =>
        let cont_67__ arg_68__ :=
          match arg_68__ with
            | pair ds r => GHC.Base.return_ (pair (Data.Foldable.foldl1 (fun n d =>
                                                                          (n GHC.Num.* GHC.Num.fromInteger 10) GHC.Num.+
                                                                          d) (Coq.Lists.List.flat_map (fun d =>
                                                                                                        cons
                                                                                                        (GHC.Char.ord d
                                                                                                        GHC.Num.-
                                                                                                        GHC.Char.ord
                                                                                                        (GHC.Char.hs_char__
                                                                                                        "0")) nil) ds))
                                                  r)
          end in
        nonnull GHC.Unicode.isDigit s GHC.Base.>>= cont_67__ in
    let readExp' :=
      fun arg_71__ =>
        match arg_71__ with
          | cons ("+"%char) s => readDec s
          | cons ("-"%char) s => let cont_73__ arg_74__ :=
                                   match arg_74__ with
                                     | pair k t => GHC.Base.return_ (pair (negate k) t)
                                   end in
                                 readDec s GHC.Base.>>= cont_73__
          | s => readDec s
        end in
    let readExp :=
      fun arg_78__ =>
        let j_80__ :=
          match arg_78__ with
            | s => GHC.Base.return_ (pair (GHC.Num.fromInteger 0) s)
          end in
        match arg_78__ with
          | cons e s => if Data.Foldable.elem e (GHC.Base.hs_string__ "eE") : bool
                        then readExp' s
                        else j_80__
          | _ => j_80__
        end in
    let readFix :=
      fun r =>
        let cont_83__ arg_84__ :=
          match arg_84__ with
            | pair ds s => let cont_85__ arg_86__ :=
                             match arg_86__ with
                               | pair ds' t => GHC.Base.return_ (pair (pair (Text.Read.read
                                                                            (Coq.Init.Datatypes.app ds ds'))
                                                                            (Data.Foldable.length ds')) t)
                             end in
                           lexDotDigits s GHC.Base.>>= cont_85__
          end in
        lexDecDigits r GHC.Base.>>= cont_83__ in
    let cont_88__ arg_89__ :=
      match arg_89__ with
        | pair (pair n d) s => let cont_90__ arg_91__ :=
                                 match arg_91__ with
                                   | pair k t => GHC.Base.return_ (pair ((n GHC.Real.% GHC.Num.fromInteger 1)
                                                                        GHC.Num.* (GHC.Num.fromInteger 10 GHC.Real.^^ (k
                                                                        GHC.Num.- d))) t)
                                 end in
                               readExp s GHC.Base.>>= cont_90__
      end in
    readFix r GHC.Base.>>= cont_88__.

Definition readRational : GHC.Base.String -> GHC.Real.Rational :=
  fun top_s =>
    let read_me :=
      fun s =>
        let scrut_95__ :=
          (let cont_93__ arg_94__ :=
            match arg_94__ with
              | pair x "" => GHC.Base.return_ x
              | _ => missingValue (GHC.Base.hs_string__
                                  "Partial pattern match in `do' notation")
            end in
          readRational__ s GHC.Base.>>= cont_93__) in
        match scrut_95__ with
          | cons x nil => x
          | nil => GHC.Err.error (Coq.Init.Datatypes.app (GHC.Base.hs_string__
                                                         "readRational: no parse:") top_s)
          | _ => GHC.Err.error (Coq.Init.Datatypes.app (GHC.Base.hs_string__
                                                       "readRational: ambiguous parse:") top_s)
        end in
    match top_s with
      | cons ("-"%char) xs => negate (read_me xs)
      | xs => read_me xs
    end.

Definition reslash : Direction -> GHC.Base.String -> GHC.Base.String :=
  fun d =>
    let slash :=
      match d with
        | Forwards => GHC.Char.hs_char__ "/"
        | Backwards => GHC.Char.hs_char__ "\"
      end in
    let f :=
      fix f arg_31__
            := match arg_31__ with
                 | cons ("/"%char) xs => cons slash (f xs)
                 | cons ("\"%char) xs => cons slash (f xs)
                 | cons x xs => cons x (f xs)
                 | "" => GHC.Base.hs_string__ ""
               end in
    f.

Definition seqList {a} {b} : list a -> b -> b :=
  fix seqList arg_120__ arg_121__
        := match arg_120__ , arg_121__ with
             | nil , b => b
             | cons x xs , b => GHC.Prim.seq x (seqList xs b)
           end.

Definition singleton {a} : a -> list a :=
  fun x => cons x nil.

Definition sizedComplement {bv} `{Data.Bits.Bits bv} : bv -> bv -> bv :=
  fun vector_mask vect => Data.Bits.xor vector_mask vect.

Definition restrictedDamerauLevenshteinDistanceWorker {bv} `{Data.Bits.Bits bv}
                                                      `{GHC.Num.Num bv} : Data.IntMap.Base.IntMap bv -> bv -> bv -> (bv
                                                                          * bv * bv * bv *
                                                                          GHC.Num.Int)%type -> GHC.Char.Char -> (bv * bv
                                                                          * bv * bv * GHC.Num.Int)%type :=
  fun arg_136__ arg_137__ arg_138__ arg_139__ arg_140__ =>
    match arg_136__ , arg_137__ , arg_138__ , arg_139__ , arg_140__ with
      | str1_mvs , top_bit_mask , vector_mask , pair (pair (pair (pair pm d0) vp) vn)
                                                     distance , char2 => let pm' :=
                                                                           Data.IntMap.Base.findWithDefault
                                                                           (GHC.Num.fromInteger 0) (GHC.Char.ord char2)
                                                                           str1_mvs in
                                                                         let d0' :=
                                                                           ((((Data.Bits.shiftL ((sizedComplement
                                                                                                vector_mask d0)
                                                                                                Data.Bits..&. pm')
                                                                                                (GHC.Num.fromInteger 1))
                                                                           Data.Bits..&. pm) Data.Bits..|.
                                                                           (Data.Bits.xor (((pm' Data.Bits..&. vp)
                                                                                          GHC.Num.+ vp) Data.Bits..&.
                                                                                          vector_mask) vp))
                                                                           Data.Bits..|. pm') Data.Bits..|. vn in
                                                                         let hp' :=
                                                                           vn Data.Bits..|. sizedComplement vector_mask
                                                                           (d0' Data.Bits..|. vp) in
                                                                         let hp'_shift :=
                                                                           ((Data.Bits.shiftL hp' (GHC.Num.fromInteger
                                                                                              1)) Data.Bits..|.
                                                                           GHC.Num.fromInteger 1) Data.Bits..&.
                                                                           vector_mask in
                                                                         let distance' :=
                                                                           if (hp' Data.Bits..&. top_bit_mask)
                                                                              GHC.Base./= GHC.Num.fromInteger 0 : bool
                                                                           then distance GHC.Num.+ GHC.Num.fromInteger 1
                                                                           else distance in
                                                                         let hn' := d0' Data.Bits..&. vp in
                                                                         let hn'_shift :=
                                                                           (Data.Bits.shiftL hn' (GHC.Num.fromInteger
                                                                                             1)) Data.Bits..&.
                                                                           vector_mask in
                                                                         let distance'' :=
                                                                           if (hn' Data.Bits..&. top_bit_mask)
                                                                              GHC.Base./= GHC.Num.fromInteger 0 : bool
                                                                           then distance' GHC.Num.- GHC.Num.fromInteger
                                                                                1
                                                                           else distance' in
                                                                         let vp' :=
                                                                           hn'_shift Data.Bits..|. sizedComplement
                                                                           vector_mask (d0' Data.Bits..|. hp'_shift) in
                                                                         let vn' := d0' Data.Bits..&. hp'_shift in
                                                                         GHC.Prim.seq str1_mvs GHC.Base.$ (GHC.Prim.seq
                                                                         top_bit_mask GHC.Base.$ (GHC.Prim.seq
                                                                         vector_mask GHC.Base.$ (GHC.Prim.seq pm'
                                                                         GHC.Base.$ (GHC.Prim.seq d0' GHC.Base.$
                                                                         (GHC.Prim.seq vp' GHC.Base.$ (GHC.Prim.seq vn'
                                                                         GHC.Base.$ (GHC.Prim.seq distance'' GHC.Base.$
                                                                         (GHC.Prim.seq char2 GHC.Base.$ pair (pair (pair
                                                                                                                   (pair
                                                                                                                   pm'
                                                                                                                   d0')
                                                                                                                   vp')
                                                                                                                   vn')
                                                                                                             distance''))))))))
    end.

Definition restrictedDamerauLevenshteinDistance' {bv} `{Data.Bits.Bits bv}
                                                 `{GHC.Num.Num bv}
    : bv -> GHC.Num.Int -> GHC.Num.Int -> GHC.Base.String -> GHC.Base.String -> GHC.Num.Int :=
  fun _bv_dummy m n str1 str2 =>
    let extractAnswer :=
      fun arg_153__ =>
        match arg_153__ with
          | pair (pair (pair (pair _ _) _) _) distance => distance
        end in
    let top_bit_mask :=
      GHC.Base.asTypeOf (Data.Bits.shiftL (GHC.Num.fromInteger 1) (m GHC.Num.-
                                          GHC.Num.fromInteger 1)) _bv_dummy in
    match (GHC.Num.fromInteger 2 GHC.Real.^ m) GHC.Num.- GHC.Num.fromInteger 1 with
      | (vector_mask as m_ones) => let j_157__ :=
                                     extractAnswer GHC.Base.$ Data.Foldable.foldl'
                                     (restrictedDamerauLevenshteinDistanceWorker (matchVectors str1) top_bit_mask
                                     vector_mask) (pair (pair (pair (pair (GHC.Num.fromInteger 0)
                                                                          (GHC.Num.fromInteger 0)) m_ones)
                                                              (GHC.Num.fromInteger 0)) m) str2 in
                                   match str1 with
                                     | nil => n
                                   end
    end.

Definition restrictedDamerauLevenshteinDistanceWithLengths
    : GHC.Num.Int -> GHC.Num.Int -> GHC.Base.String -> GHC.Base.String -> GHC.Num.Int :=
  fun m n str1 str2 =>
    let j_159__ :=
      if m GHC.Base.<= GHC.Num.fromInteger 32 : bool
      then restrictedDamerauLevenshteinDistance' (GHC.Err.undefined : GHC.Word.Word32)
           n m str2 str1
      else restrictedDamerauLevenshteinDistance' (GHC.Err.undefined : GHC.Num.Integer)
           n m str2 str1 in
    if m GHC.Base.<= n : bool
    then if n GHC.Base.<= GHC.Num.fromInteger 32 : bool
         then restrictedDamerauLevenshteinDistance' (GHC.Err.undefined : GHC.Word.Word32)
              m n str1 str2
         else restrictedDamerauLevenshteinDistance' (GHC.Err.undefined : GHC.Num.Integer)
              m n str1 str2
    else j_159__.

Definition restrictedDamerauLevenshteinDistance
    : GHC.Base.String -> GHC.Base.String -> GHC.Num.Int :=
  fun str1 str2 =>
    let n := Data.Foldable.length str2 in
    let m := Data.Foldable.length str1 in
    restrictedDamerauLevenshteinDistanceWithLengths m n str1 str2.

Definition fuzzyLookup {a} : GHC.Base.String -> list (GHC.Base.String *
                                                     a)%type -> list a :=
  fun user_entered possibilites =>
    let mAX_RESULTS := GHC.Num.fromInteger 3 in
    let fuzzy_threshold :=
      GHC.Real.truncate GHC.Base.$ (GHC.Real.fromIntegral (Data.Foldable.length
                                                          user_entered GHC.Num.+ GHC.Num.fromInteger 2) GHC.Real./
      (GHC.Num.fromInteger 4 : GHC.Real.Rational)) in
    GHC.Base.map Data.Tuple.fst GHC.Base.$ (GHC.List.take mAX_RESULTS GHC.Base.$
    Data.OldList.sortBy (Data.Ord.comparing Data.Tuple.snd)
    (let cont_166__ arg_167__ :=
      match arg_167__ with
        | pair poss_str poss_val => let distance :=
                                      restrictedDamerauLevenshteinDistance poss_str user_entered in
                                    if distance GHC.Base.<= fuzzy_threshold : bool
                                    then cons (pair poss_val distance) nil
                                    else nil
      end in
    Coq.Lists.List.flat_map cont_166__ possibilites)).

Definition fuzzyMatch : GHC.Base.String -> list GHC.Base.String -> list
                        GHC.Base.String :=
  fun key vals =>
    fuzzyLookup key (Coq.Lists.List.flat_map (fun v => cons (pair v v) nil) vals).

Definition snd3 {b} {d} {a} {c} : (b -> d) -> (a * b * c)%type -> (a * d *
                                  c)%type :=
  fun arg_498__ arg_499__ =>
    match arg_498__ , arg_499__ with
      | f , pair (pair a b) c => pair (pair a (f b)) c
    end.

Definition sndOf3 {a} {b} {c} : (a * b * c)%type -> b :=
  fun arg_508__ => match arg_508__ with | pair (pair _ b) _ => b end.

Definition snocView {a} : list a -> option (list a * a)%type :=
  fun arg_246__ =>
    match arg_246__ with
      | nil => None
      | xs => let go :=
                fix go arg_247__ arg_248__
                      := match arg_247__ , arg_248__ with
                           | acc , cons x nil => Some (pair (GHC.List.reverse acc) x)
                           | acc , cons x xs => go (cons x acc) xs
                           | _ , nil => Panic.panic (GHC.Base.hs_string__ "Util: snocView")
                         end in
              go nil xs
    end.

Definition spanEnd {a} : (a -> bool) -> list a -> (list a * list a)%type :=
  fun p l =>
    let go :=
      fix go arg_255__ arg_256__ arg_257__ arg_258__
            := match arg_255__ , arg_256__ , arg_257__ , arg_258__ with
                 | yes , _rev_yes , rev_no , nil => pair yes (GHC.List.reverse rev_no)
                 | yes , rev_yes , rev_no , cons x xs => let j_260__ :=
                                                           go xs nil (cons x (Coq.Init.Datatypes.app rev_yes rev_no))
                                                           xs in
                                                         if p x : bool
                                                         then go yes (cons x rev_yes) rev_no xs
                                                         else j_260__
               end in
    go l nil nil l.

Definition split : GHC.Char.Char -> GHC.Base.String -> list GHC.Base.String :=
  fix split c s
        := match GHC.List.break (fun arg_239__ => arg_239__ GHC.Base.== c) s with
             | pair chunk rest => match rest with
                                    | nil => cons chunk nil
                                    | cons _ rest => cons chunk (split c rest)
                                  end
           end.

Definition looksLikePackageName : GHC.Base.String -> bool :=
  Data.Foldable.all (Data.Foldable.all GHC.Unicode.isAlphaNum <&&> (negb
                    GHC.Base.∘ (Data.Foldable.all GHC.Unicode.isDigit))) GHC.Base.∘ split
  (GHC.Char.hs_char__ "-").

Definition splitAtList {b} {a} : list b -> list a -> (list a * list a)%type :=
  fix splitAtList arg_272__ arg_273__
        := match arg_272__ , arg_273__ with
             | nil , xs => pair nil xs
             | _ , (nil as xs) => pair xs xs
             | cons _ xs , cons y ys => match splitAtList xs ys with
                                          | pair ys' ys'' => pair (cons y ys') ys''
                                        end
           end.

Definition splitEithers {a} {b} : list (Data.Either.Either a b) -> (list a *
                                  list b)%type :=
  fix splitEithers arg_449__
        := match arg_449__ with
             | nil => pair nil nil
             | cons e es => match splitEithers es with
                              | pair xs ys => match e with
                                                | Data.Either.Left x => pair (cons x xs) ys
                                                | Data.Either.Right y => pair xs (cons y ys)
                                              end
                            end
           end.

Definition splitLongestPrefix
    : GHC.Base.String -> (GHC.Char.Char -> bool) -> (GHC.Base.String *
      GHC.Base.String)%type :=
  fun str pred =>
    match GHC.List.break pred (GHC.List.reverse str) with
      | pair r_suf r_pre => let j_40__ :=
                              pair (GHC.List.reverse (GHC.List.tail r_pre)) (GHC.List.reverse r_suf) in
                            if Data.Foldable.null r_pre : bool
                            then pair str nil
                            else j_40__
    end.

Definition stretchZipWith {a} {b} {c}
    : (a -> bool) -> b -> (a -> b -> c) -> list a -> list b -> list c :=
  fix stretchZipWith arg_398__ arg_399__ arg_400__ arg_401__ arg_402__
        := match arg_398__ , arg_399__ , arg_400__ , arg_401__ , arg_402__ with
             | _ , _ , _ , nil , _ => nil
             | p , z , f , cons x xs , ys => let j_405__ :=
                                               match ys with
                                                 | nil => nil
                                                 | cons y ys => cons (f x y) (stretchZipWith p z f xs ys)
                                               end in
                                             if p x : bool
                                             then cons (f x z) (stretchZipWith p z f xs ys)
                                             else j_405__
           end.

Definition takeList {b} {a} : list b -> list a -> list a :=
  fix takeList arg_283__ arg_284__
        := match arg_283__ , arg_284__ with
             | nil , _ => nil
             | cons _ xs , ls => match ls with
                                   | nil => nil
                                   | cons y ys => cons y (takeList xs ys)
                                 end
           end.

Definition thdOf3 {a} {b} {c} : (a * b * c)%type -> c :=
  fun arg_506__ => match arg_506__ with | pair (pair _ _) c => c end.

Definition thenCmp : comparison -> comparison -> comparison :=
  fun arg_234__ arg_235__ =>
    match arg_234__ , arg_235__ with
      | Eq , ordering => ordering
      | ordering , _ => ordering
    end.

Definition third3 {c} {d} {a} {b} : (c -> d) -> (a * b * c)%type -> (a * b *
                                    d)%type :=
  fun arg_494__ arg_495__ =>
    match arg_494__ , arg_495__ with
      | f , pair (pair a b) c => pair (pair a b) (f c)
    end.

Definition transitiveClosure {a} : (a -> list a) -> (a -> a -> bool) -> list
                                   a -> list a :=
  fun succ eq xs =>
    let is_in :=
      fix is_in arg_307__ arg_308__
            := match arg_307__ , arg_308__ with
                 | _ , nil => false
                 | x , cons y ys => let j_309__ := is_in x ys in
                                    if eq x y : bool
                                    then true
                                    else j_309__
               end in
    let go :=
      fix go arg_312__ arg_313__
            := match arg_312__ , arg_313__ with
                 | done , nil => done
                 | done , cons x xs => let j_314__ :=
                                         go (cons x done) (Coq.Init.Datatypes.app (succ x) xs) in
                                       if is_in x done : bool
                                       then go done xs
                                       else j_314__
               end in
    go nil xs.

Definition uncurry3 {a} {b} {c} {d} : (a -> b -> c -> d) -> (a * b *
                                      c)%type -> d :=
  fun arg_490__ arg_491__ =>
    match arg_490__ , arg_491__ with
      | f , pair (pair a b) c => f a b c
    end.

Definition unzipWith {a} {b} {c} : (a -> b -> c) -> list (a * b)%type -> list
                                   c :=
  fun f pairs =>
    GHC.Base.map (fun arg_124__ => match arg_124__ with | pair a b => f a b end)
    pairs.

Definition zipEqual {a} {b} : GHC.Base.String -> list a -> list b -> list (a *
                                                                          b)%type :=
  fun arg_446__ => GHC.List.zip.

Definition zipLazy {a} {b} : list a -> list b -> list (a * b)%type :=
  fix zipLazy arg_439__ arg_440__
        := match arg_439__ , arg_440__ with
             | nil , _ => nil
             | cons x xs , cons y ys => cons (pair x y) (zipLazy xs ys)
             | _ , _ => patternFailure
           end.

Definition zipWith3Equal {a} {b} {c} {d}
    : GHC.Base.String -> (a -> b -> c -> d) -> list a -> list b -> list c -> list
      d :=
  fun arg_444__ => GHC.List.zipWith3.

Definition zipWith3Lazy {a} {b} {c} {d} : (a -> b -> c -> d) -> list a -> list
                                          b -> list c -> list d :=
  fix zipWith3Lazy arg_428__ arg_429__ arg_430__ arg_431__
        := match arg_428__ , arg_429__ , arg_430__ , arg_431__ with
             | _ , nil , _ , _ => nil
             | f , cons a as_ , cons b bs , cons c cs => cons (f a b c) (zipWith3Lazy f as_
                                                              bs cs)
             | _ , _ , _ , _ => patternFailure
           end.

Definition zipWith4Equal {a} {b} {c} {d} {e}
    : GHC.Base.String -> (a -> b -> c -> d -> e) -> list a -> list b -> list
      c -> list d -> list e :=
  fun arg_443__ => Data.OldList.zipWith4.

Definition zipWithAndUnzip {a} {b} {c} {d} : (a -> b -> (c * d)%type) -> list
                                             a -> list b -> (list c * list d)%type :=
  fix zipWithAndUnzip arg_370__ arg_371__ arg_372__
        := match arg_370__ , arg_371__ , arg_372__ with
             | f , cons a as_ , cons b bs => match zipWithAndUnzip f as_ bs with
                                               | pair rs1 rs2 => match f a b with
                                                                   | pair r1 r2 => pair (cons r1 rs1) (cons r2 rs2)
                                                                 end
                                             end
             | _ , _ , _ => pair nil nil
           end.

Definition zipWithEqual {a} {b} {c} : GHC.Base.String -> (a -> b -> c) -> list
                                      a -> list b -> list c :=
  fun arg_445__ => GHC.List.zipWith.

Definition zipWithLazy {a} {b} {c} : (a -> b -> c) -> list a -> list b -> list
                                     c :=
  fix zipWithLazy arg_434__ arg_435__ arg_436__
        := match arg_434__ , arg_435__ , arg_436__ with
             | _ , nil , _ => nil
             | f , cons a as_ , cons b bs => cons (f a b) (zipWithLazy f as_ bs)
             | _ , _ , _ => patternFailure
           end.

Module Notations.
Notation "'_Util.<&&>_'" := (op_zlzazazg__).
Infix "Util.<&&>" := (_<&&>_) (at level 99).
Notation "'_Util.<||>_'" := (op_zlzbzbzg__).
Infix "Util.<||>" := (_<||>_) (at level 99).
End Notations.

(* Unbound variables:
     Eq Gt Lt None Some abstractDataType andb bool comparison cons false list negate
     negb nil op_zt__ option orb pair textEncodingName true tt unit
     Coq.Init.Datatypes.app Coq.Lists.List.flat_map Data.Bits.Bits
     Data.Bits.op_zizazi__ Data.Bits.op_zizbzi__ Data.Bits.shiftL Data.Bits.shiftR
     Data.Bits.xor Data.Data.Constr Data.Data.DataType Data.Data.Prefix
     Data.Data.mkConstr Data.Data.mkDataType Data.Either.Either Data.Either.Left
     Data.Either.Right Data.Foldable.all Data.Foldable.elem Data.Foldable.foldl'
     Data.Foldable.foldl1 Data.Foldable.foldr Data.Foldable.length
     Data.Foldable.notElem Data.Foldable.null Data.IORef.atomicModifyIORef'
     Data.IntMap.Base.IntMap Data.IntMap.Base.empty Data.IntMap.Base.findWithDefault
     Data.IntMap.Base.insertWith Data.OldList.sortBy Data.OldList.zipWith4
     Data.Ord.comparing Data.Set.Base.fromList Data.Set.Base.toAscList
     Data.Time.Clock.UTC.UTCTime Data.Traversable.mapAccumL Data.Tuple.fst
     Data.Tuple.snd Exception.catchIO GHC.Base.Applicative GHC.Base.Eq_
     GHC.Base.Monad GHC.Base.Ord GHC.Base.String GHC.Base.asTypeOf GHC.Base.const
     GHC.Base.fmap GHC.Base.id GHC.Base.liftA2 GHC.Base.liftM GHC.Base.map
     GHC.Base.op_z2218U__ GHC.Base.op_zd__ GHC.Base.op_zeze__ GHC.Base.op_zgze__
     GHC.Base.op_zgzgze__ GHC.Base.op_zl__ GHC.Base.op_zlze__ GHC.Base.op_zsze__
     GHC.Base.return_ GHC.Char.Char GHC.Char.chr GHC.Char.ord GHC.Err.error
     GHC.Err.undefined GHC.Exts.sortWith GHC.IO.Encoding.mkTextEncoding
     GHC.IO.Exception.ioError GHC.IO.Handle.hGetEncoding GHC.IO.Handle.hSetEncoding
     GHC.IO.Handle.Types.Handle GHC.IO.Unsafe.unsafePerformIO GHC.IORef.IORef
     GHC.IORef.newIORef GHC.Int.Int32 GHC.Int.Int64 GHC.List.break GHC.List.drop
     GHC.List.dropWhile GHC.List.head GHC.List.replicate GHC.List.reverse
     GHC.List.span GHC.List.splitAt GHC.List.tail GHC.List.take GHC.List.zip
     GHC.List.zipWith GHC.List.zipWith3 GHC.Num.Int GHC.Num.Integer GHC.Num.Num
     GHC.Num.op_zm__ GHC.Num.op_zp__ GHC.Num.op_zt__ GHC.Prim.seq GHC.Read.Read
     GHC.Real.Rational GHC.Real.div GHC.Real.fromIntegral GHC.Real.mod_
     GHC.Real.op_zc__ GHC.Real.op_zczc__ GHC.Real.op_zs__ GHC.Real.op_zv__
     GHC.Real.truncate GHC.Show.show GHC.Types.IO GHC.Unicode.isAlphaNum
     GHC.Unicode.isDigit GHC.Unicode.isSpace GHC.Unicode.isUpper GHC.Word.Word32
     GHC.Word.Word8 Panic.assertPanic Panic.panic System.Directory.doesDirectoryExist
     System.Directory.getModificationTime System.FilePath.Posix.dropFileName
     System.FilePath.Posix.joinPath System.FilePath.Posix.op_zlzszg__
     System.FilePath.Posix.splitFileName System.FilePath.Posix.splitPath
     System.FilePath.Posix.takeDirectory System.IO.Error.isDoesNotExistError
     Text.ParserCombinators.ReadP.ReadS Text.Read.read Text.Read.reads
*)
