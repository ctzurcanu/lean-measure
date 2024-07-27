import Batteries.Data.HashMap.Basic
import Mathlib



-- Define a type alias for HashMap for convenience
def dict (key value: Type)  [BEq key] [Hashable key] := Batteries.HashMap key value

-- Function to create an empty HashMap
def empty_dict {key: Type} [BEq key] [Hashable key] : dict key value :=
  Batteries.HashMap.empty

def removeZeroValues {key value: Type} [BEq key] [Hashable key] [BEq value] (d : dict key value) (val0 : value): dict key value :=
  -- Fold over the hash map to filter out entries with value val0
  d.fold (fun acc k v =>
    if v != val0 then acc.insert k v else acc) empty_dict

-- Define the Repr instance for dict
instance {key value : Type} [BEq key] [Hashable key] [Repr key] [Repr value] : Repr (dict key value) where
  reprPrec d _ := repr d.toList

def eqHashMaps {K V : Type} [BEq K] [Hashable K] [BEq V] (m1 m2 : Batteries.HashMap K V) : Bool :=
  if m1.size != m2.size then false
  else m1.fold (fun acc k v1 =>
    match acc, m2.find? k with
    | false, _         => false
    | _, none          => false
    | _, some v2       => acc && (v1 == v2)
  ) true

-- Function to insert a key-value pair into the HashMap
def dict_insert {key : Type} [BEq key] [Hashable key] (d : dict key value) (k : key) (v : value) : dict key value :=
  d.insert k v

-- Function to lookup a value by key in the HashMap
def dict_lookup {key value : Type} [BEq key] [Hashable key] (d : dict key value) (k : key) : Option value :=
  d.find? k


namespace measure

structure PreQuality where
  name: String
  definition: String := ""
  short: String
  unit: String
  unit_symbol: String
  deriving BEq, Hashable

def zero_dict : dict PreQuality ℤ  := empty_dict

structure Quality extends PreQuality where
  composed : dict PreQuality ℤ := zero_dict
  is_base : Bool := false

def scalar : Quality := {name:="Scalar", short:="U", unit:="u", unit_symbol:="1", composed:= empty_dict}

def canon (q : Quality) : Quality :=
  let nq := removeZeroValues q.composed 0
  if eqHashMaps nq zero_dict then
    scalar
  else
    {name:= q.name, short:= q.short, unit:= q.unit, unit_symbol:= q.unit_symbol, composed:= nq}

def preToQ (pq: PreQuality) : Quality :=
  {name:= pq.name, short:= pq.short, unit:= pq.unit, unit_symbol:= pq.unit_symbol, composed:= (dict_insert zero_dict pq 1), is_base:= true}

def QtoString (q : Quality) : String :=
  let lst1 := q.composed.fold (fun acc k v => (k.unit_symbol ++ "^" ++ (toString v)):: acc) []
  let lst2 := lst1.map toString
  q.name ++ " " ++ q.short ++ " " ++ q.unit  ++ " " ++  q.unit_symbol ++ " " ++  String.intercalate "·" lst2 ++ " " ++ q.definition

def mergeHashMaps (m1 m2 : dict PreQuality Int) : dict PreQuality Int :=
  removeZeroValues
    (m1.fold (fun acc k v1 =>
      match m2.find? k with
      | some v2 => acc.insert k (v1 + v2)
      | none    => acc.insert k v1) m2)
      0


-- Define the function to calculate the difference between two hash maps
def diffHashMaps (m1 m2 : dict PreQuality Int) : dict PreQuality Int :=
  -- Define a helper function to process key-value pairs and calculate the difference
  let processPair (acc : dict PreQuality Int) (k : PreQuality) (v1 : Int) : dict PreQuality Int :=
    match m2.find? k with
    | some v2 => acc.insert k (v1 - v2)  -- Calculate difference if key exists in m2
    | none    => acc.insert k v1         -- Keep value if key does not exist in m2

  -- Use fold to process key-value pairs from m1
  let intermediateResult := m1.fold (fun acc k v1 => processPair acc k v1) empty_dict

  -- Add keys from m2 that are not in m1 with negative values
  let finalResult := m2.fold (fun acc k v2 =>
    match m1.find? k with
    | some _ => acc  -- Key exists in m1, so we don't need to add it
    | none   => acc.insert k (-v2)  -- Key does not exist in m1, add negative value
  ) intermediateResult

  removeZeroValues finalResult 0

def mulQ (p : Quality) (q : Quality) :  Quality :=
  canon {composed:= mergeHashMaps p.composed q.composed,name:= p.name ++ "·" ++ q.name, short:=p.short ++ "·" ++ q.short, unit:=p.unit ++ "·" ++ q.unit, unit_symbol:=p.unit_symbol ++ "·" ++ q.unit_symbol}

def divQ (p : Quality) (q : Quality) :  Quality :=
  canon {composed:= diffHashMaps p.composed q.composed,name:= p.name ++ "/" ++ q.name, short:=p.short ++ "/" ++ q.short, unit:=p.unit ++ "·" ++ q.unit, unit_symbol:=p.unit_symbol ++ "/" ++ q.unit_symbol}

def preforced: PreQuality := {name:="Non-Quality", short:="N", unit:="none", unit_symbol:="n"}

def forced: Quality := preToQ preforced

def prelength: PreQuality := {name:="Length", short:="L", unit:="metre", unit_symbol:="m"}

def length: Quality := preToQ prelength

def premass: PreQuality := {name:="Mass", short:="M", unit:="kilogram", unit_symbol:="kg"}

def mass: Quality := preToQ premass

def pretime: PreQuality := {name:="Time", short:="T", unit:="second", unit_symbol:="s"}

def time: Quality := preToQ pretime

def preecurrent: PreQuality := {name:="Electric Current", short:="I", unit:="ampere", unit_symbol:="A"}

def ecurrent: Quality := preToQ preecurrent

def pretemp: PreQuality := {name:="Therodinamic Temperature", short:="Θ", unit:="kelvin", unit_symbol:="K"}

def temp: Quality := preToQ pretemp

def preamsubst: PreQuality := {name:="Amount of Substance", short:="N", unit:="mole", unit_symbol:="mol"}

def amsubst: Quality := preToQ preamsubst

def preilum: PreQuality := {name:="Luminous Intensity", short:="J", unit:="candela", unit_symbol:="cd"}

def ilum: Quality := preToQ preilum

def equal (p : Quality) (q : Quality): Bool :=
  eqHashMaps p.composed q.composed

def velocity: Quality := {name:="Velocity", short:="v", unit:="meter/second", unit_symbol:="m/s", composed:=  dict_insert (dict_insert zero_dict prelength 1)  pretime (-1)}

def velocity2: Quality := divQ length time

#eval QtoString velocity
#eval QtoString velocity2
#eval equal velocity velocity2

structure Measure (α : Type) [Inhabited α] where
  quality: Quality
  quantity: α := default

def non_measure [Inhabited α] : Measure α :=
  { quality := forced, quantity := default }


def add {α : Type} [Inhabited α] (m: Measure α ) (n: Measure α ) [HAdd α α α]: Measure α :=
  if equal m.quality n.quality then
    let q:α := m.quantity + n.quantity
    {quality:=m.quality, quantity:= q}
  else
    non_measure

def sub {α : Type} [Inhabited α] (m: Measure α ) (n: Measure α ) [HSub α α α]: Measure α :=
  if equal m.quality n.quality then
    let q:α := m.quantity - n.quantity
    {quality:=m.quality, quantity:= q}
  else
    non_measure

def mul {α : Type} [Inhabited α] (m: Measure α ) (n: Measure α ) [HDiv α α α]: Measure α :=
  {quality:= {composed:= mergeHashMaps m.quality.composed n.quality.composed,name:= n.quality.name ++ "·" ++ m.quality.name, short:="", unit:="", unit_symbol:=""}, quantity:= n.quantity / m.quantity}

def div {α : Type} [Inhabited α] (m: Measure α ) (n: Measure α ) [HDiv α α α]: Measure α :=
  {quality:= divQ m.quality n.quality, quantity:= n.quantity / m.quantity}

def toString {α : Type} [Inhabited α] (m : Measure α ): String :=
  -- let val := α
  let unit := QtoString m.quality
  (m.quality.name) ++ ": " ++ unit

def m_m1 : Measure Float := {quality:= mass, quantity:= 10.6}

def m_m2 : Measure Float := {quality:= mass, quantity:= 4.16}

def l_m2 : Measure Float := {quality:= length, quantity:= 14.6}

def t_m2 : Measure Float := {quality:= time, quantity:= 4.6}

def m_m3 := add m_m1 m_m2

def m_m4 := mul m_m1 m_m2

def v_m5 := div l_m2 t_m2

def m_m6 := add m_m1 l_m2

def u_m5 := div m_m2 m_m2

#eval QtoString m_m3.quality
#eval m_m3.quantity

#eval QtoString m_m4.quality
#eval m_m4.quantity

#eval QtoString v_m5.quality
#eval v_m5.quantity

#eval QtoString m_m6.quality
#eval m_m6.quantity

#eval QtoString u_m5.quality
#eval u_m5.quantity
