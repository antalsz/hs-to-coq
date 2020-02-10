Require Export BL.

Require Import String.

Axiom bytestring_string_correspondance : ByteString -> string -> Prop.

Axiom to_string : forall b : ByteString, exists s : string,
      bytestring_string_correspondance b s.

Axiom from_string : forall s : string, exists b : ByteString,
      bytestring_string_correspondance b s.

Axiom equal_length : forall b s,
    bytestring_string_correspondance b s ->
    length b = length s.
