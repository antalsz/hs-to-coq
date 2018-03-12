#!/usr/bin/env perl

$imports = <<'END_IMPORTS';
import qualified Data.Char
import qualified Data.Bits
import qualified Prelude
END_IMPORTS

while (<>) {
    s/import qualified Prelude/$imports/;
    s/unsafeCoerce :: a -> b/--unsafeCoerce :: a -> b/;
    print;
}
