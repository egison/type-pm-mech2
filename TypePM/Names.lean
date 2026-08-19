import Std

/-!
# Names used by data and pattern-matching declarations

The five declaration categories deliberately use different wrapper types.
Consequently, equal source spellings such as the data constructor `nil` and
the pattern constructor `nil` cannot be confused by later lookup functions.
-/

namespace TypePM

/-- The name of a type-level data former, such as `Bool` or `List`. -/
structure DataFormer where
  name : String
deriving Repr, DecidableEq

/-- The name of a value-level data constructor, such as `true` or `cons`. -/
structure DataCtor where
  name : String
deriving Repr, DecidableEq

/-- The name of a capability-level pattern former, such as `List`. -/
structure PatternFormer where
  name : String
deriving Repr, DecidableEq

/-- The name of a pattern constructor, such as `nil`, `cons`, or `join`. -/
structure PatternCtor where
  name : String
deriving Repr, DecidableEq

/-- The name of a pattern function.  It remains distinct from pattern
constructor names even when the source spellings happen to agree. -/
structure PatternFunName where
  name : String
deriving Repr, DecidableEq

instance : ToString DataFormer where
  toString := DataFormer.name

instance : ToString DataCtor where
  toString := DataCtor.name

instance : ToString PatternFormer where
  toString := PatternFormer.name

instance : ToString PatternCtor where
  toString := PatternCtor.name

instance : ToString PatternFunName where
  toString := PatternFunName.name

namespace DataFormer

/-- The paper's Boolean data former. -/
def bool : DataFormer := ⟨"Bool"⟩

/-- The paper's list data former. -/
def list : DataFormer := ⟨"List"⟩

theorem toString_bool : toString bool = "Bool" := by
  rfl

theorem toString_list : toString list = "List" := by
  rfl

theorem bool_ne_list : bool ≠ list := by
  decide

end DataFormer

namespace DataCtor

/-- The paper's Boolean constructor `true`. -/
def «true» : DataCtor := ⟨"true"⟩

/-- The paper's Boolean constructor `false`. -/
def «false» : DataCtor := ⟨"false"⟩

/-- The paper's empty-list data constructor. -/
def nil : DataCtor := ⟨"nil"⟩

/-- The paper's nonempty-list data constructor. -/
def cons : DataCtor := ⟨"cons"⟩

theorem toString_true : toString «true» = "true" := by
  rfl

theorem toString_false : toString «false» = "false" := by
  rfl

theorem toString_nil : toString nil = "nil" := by
  rfl

theorem toString_cons : toString cons = "cons" := by
  rfl

theorem canonical_pairwise_distinct :
    List.Pairwise (· ≠ ·) [«true», «false», nil, cons] := by
  decide

end DataCtor

namespace PatternFormer

/-- The paper's list pattern former. -/
def list : PatternFormer := ⟨"List"⟩

theorem toString_list : toString list = "List" := by
  rfl

end PatternFormer

namespace PatternCtor

/-- The paper's empty-list pattern constructor. -/
def nil : PatternCtor := ⟨"nil"⟩

/-- The paper's head-tail pattern constructor. -/
def cons : PatternCtor := ⟨"cons"⟩

/-- The paper's prefix-suffix pattern constructor. -/
def join : PatternCtor := ⟨"join"⟩

theorem toString_nil : toString nil = "nil" := by
  rfl

theorem toString_cons : toString cons = "cons" := by
  rfl

theorem toString_join : toString join = "join" := by
  rfl

theorem canonical_pairwise_distinct :
    List.Pairwise (· ≠ ·) [nil, cons, join] := by
  decide

end PatternCtor

namespace NamesRegression

/-- Data and pattern constructors may have equal spellings without sharing a
name type.  The type annotations below are checked independently. -/
def dataNil : DataCtor := DataCtor.nil

def patternNil : PatternCtor := PatternCtor.nil

theorem nil_spellings_agree : dataNil.name = patternNil.name := by
  rfl

/-- Data and pattern formers likewise remain separate despite both using the
paper spelling `List`. -/
def dataList : DataFormer := DataFormer.list

def patternList : PatternFormer := PatternFormer.list

theorem list_spellings_agree : dataList.name = patternList.name := by
  rfl

end NamesRegression

end TypePM
