/// Errors.
module MCML.Errors

open MCML.AST

type Error =
  | UnexpectedInput
  | EndOfInputInsideString
  | EndOfInputInsideComment
  | Expected of string
  | Dummy
  | CyclicType of Type * Type
  | TupleLengthsDiffer of Type * Type
  | TypeMismatch of Type * Type
  | DuplicatePatternName of string
  | MissingPatternName of string
  | UnknownConstructor of string
  | UnknownVariable of string
  | UnknownType of string
  | UnknownTypeVariable
  | ConstructorRequiresArgument of Type
  | ConstructorDoesNotRequireArgument
  | Unmatched of string
  | Panic of string
