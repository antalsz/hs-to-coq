module PartialRecordSel where

-- Partial record selectors use 'error' in the output (which is undefined)
-- Would be better to use 'panic' (or be able to skip them entirely).

data R = R1 { a :: Bool } | R2 { b :: Bool }
