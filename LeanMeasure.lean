import Batteries.Data.HashMap.Basic
import Mathlib
-- import Mathlib.Algebra.MonoidAlgebra.Basic
-- import Mathlib.Algebra.Ring.Basic



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

-- def zeroHashMaps (m : dict PreQuality Int) : dict PreQuality Int :=
--   m.fold (fun k v1 =>
--     0)

-- def zeroInt : Int := 0

-- -- Modify the function to use a specific zero value if needed
-- def setValuesToZero (d : dict PreQuality Int) : dict PreQuality Int :=
--   let zeroValue : Int := zeroInt -- Adjust if needed for other types
--   d.fold(fun acc k v =>
--     -- Insert each key with a zero value into the accumulator
--     acc.insert k zeroInt) zero_dict

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


-- Define an instance of HMul for Quality
instance : HMul Quality Quality Quality :=
{
  hMul := mulQ
}


def divQ (p : Quality) (q : Quality) :  Quality :=
  canon {composed:= diffHashMaps p.composed q.composed,name:= p.name ++ "/" ++ q.name, short:=p.short ++ "/" ++ q.short, unit:=p.unit ++ "·" ++ q.unit, unit_symbol:=p.unit_symbol ++ "/" ++ q.unit_symbol}

instance : HDiv Quality Quality Quality :=
{
  hDiv := divQ
}

-- Define the typeclass for exponentiation with handling negative exponents
class Pow (α : Type) where
  pow : α → Int → α

-- Provide an instance of Pow for Measure
-- instance : Pow Quality  where
--   pow a 0 := {name:= a.name ++ "^" ++ "0", short:="u", unit:= (a.unit ++ "^" ++ "0"), unit_symbol:= (a.unit_symbol ++ "^" ++ "0"), composed:= zero_dict}
--   pow a n := if n > 0 then { value := a.value ^ n.toNat } else { value := 1.0 / (a.value ^ (-n).toNat) }

-- Define a custom notation for MyType exponentiation
infixl:80 " ^ " => Pow.pow

def preforced: PreQuality := {name:="Non-Quality", short:="N", unit:="none", unit_symbol:="n", definition:="This is intended as an error message."}

def forced: Quality := preToQ preforced

def predecimal: PreQuality := {name:="Decimal", short:="dec", unit:="deci", unit_symbol:="10", definition:="Powers of 10."}

def decimal: Quality := preToQ predecimal



def prelength: PreQuality := {name:="Length", short:="L", unit:="metre", unit_symbol:="m", definition:="The distance travelled by light in vacuum in 1/299792458 second."}

def length: Quality := preToQ prelength


def l_0 : Quality := length * length
#check l_0
#eval QtoString l_0

def premass: PreQuality := {name:="Mass", short:="M", unit:="kilogram", unit_symbol:="kg", definition:="The kilogram is defined by setting the Planck constant h to 6.62607015×10−34 J⋅s (J = kg⋅m2⋅s−2), given the definitions of the metre and the second."}

def mass: Quality := preToQ premass

def pretime: PreQuality := {name:="Time", short:="T", unit:="second", unit_symbol:="s", definition:="The duration of 9192631770 periods of the radiation corresponding to the transition between the two hyperfine levels of the ground state of the caesium-133 atom."}

def time: Quality := preToQ pretime

def pree_current: PreQuality := {name:="Electric Current", short:="I", unit:="ampere", unit_symbol:="A", definition:="The flow of 1/1.602176634×10−19 times the elementary charge e per second, which is approximately 6.2415090744×1018 elementary charges per second."}

def e_current: Quality := preToQ pree_current

def pretemp: PreQuality := {name:="Therodinamic Temperature", short:="Θ", unit:="kelvin", unit_symbol:="K", definition:="The kelvin is defined by setting the fixed numerical value of the Boltzmann constant k to 1.380649×10^−23 J⋅K−1, (J = kg⋅m^2⋅s^−2), given the definition of the kilogram, the metre, and the second."}

def temp: Quality := preToQ pretemp

def pream_subst: PreQuality := {name:="Amount of Substance", short:="N", unit:="mole", unit_symbol:="mol", definition:="The amount of substance of 6.02214076×10^23 elementary entities. This number is the fixed numerical value of the Avogadro constant, NA, when expressed in the unit mol^−1."}

def am_subst: Quality := preToQ pream_subst

def prelum_intensity: PreQuality := {name:="Luminous Intensity", short:="J", unit:="candela", unit_symbol:="cd", definition:="The duration of 9192631770 periods of the radiation corresponding to the transition between the two hyperfine levels of the ground state of the caesium-133 atom."}

def lum_intensity: Quality := preToQ prelum_intensity

def equal (p : Quality) (q : Quality): Bool :=
  eqHashMaps p.composed q.composed

def area0: Quality := length * length

def area: Quality := {name:="Area", short:="area", unit:="meter square", unit_symbol:="m^2", composed:= area0.composed}

def volume0: Quality := area * length

def volume: Quality := {name:="Volume", short:="volume", unit:="meter cube", unit_symbol:="m^3", composed:= volume0.composed}

def speed0: Quality := length / time

def speed: Quality := {name:="Velocity", short:="v", unit:="meter/second", unit_symbol:="m/s", composed:= speed0.composed}

def acceleration0: Quality := length / time /time

def acceleration: Quality := {name:="Acceleration", short:="a", unit:="meter/second^2", unit_symbol:="m/s^2", composed:= acceleration0.composed}

def p_angle0 := length/length

def p_angle: Quality := {name:="Plane Angle", short:="angle", unit:="radian", unit_symbol:="rad", composed:= p_angle0.composed}

def s_angle0 := length * length/(length * length)

def s_angle: Quality := {name:="Solid Angle", short:="angle", unit:="steradian", unit_symbol:="sr", composed:= s_angle0.composed}

def frequency0 := scalar / time

def frequency: Quality := {name:="Frequency", short:="frequency", unit:="hertz", unit_symbol:="Hz", composed:= frequency0.composed}

def force0 := mass * length / (time * time)

def force: Quality := {name:="Force", short:="force", unit:="newton", unit_symbol:="N", composed:= force0.composed}

def pressure0 := mass / (length * time * time)

def pressure: Quality := {name:="Pressure", short:="pressure", unit:="pascal", unit_symbol:="Pa", composed:= pressure0.composed}

def energy0 := mass *length *length / ( time * time)

def energy: Quality := {name:="Energy", short:="energy", unit:="joule", unit_symbol:="J", composed:= energy0.composed}

def power0 := mass *length *length / ( time * time * time)

def power: Quality := {name:="Power", short:="power", unit:="watt", unit_symbol:="W", composed:= power0.composed}

def e_charge0 := e_current * time

def e_charge: Quality := {name:="Electric Charge", short:="charge", unit:="coulomb", unit_symbol:="C", composed:= e_charge0.composed}

def e_potential0 := energy / e_charge

def e_potential: Quality := {name:="Electric Potential", short:="voltage", unit:="volt", unit_symbol:="V", composed:= e_potential0.composed}

def capacitance0 := e_charge / e_potential

def capacitance: Quality := {name:="Capacitance", short:="capacitance", unit:="farad", unit_symbol:="F", composed:= capacitance0.composed}

def resistance0 := e_potential / e_current

def resistance: Quality := {name:="Resistance", short:="resistance", unit:="ohm", unit_symbol:="Ω", composed:= resistance0.composed}

def conductance0 := scalar / resistance

def conductance: Quality := {name:="Electrical Conductance", short:="conductance", unit:="siemens", unit_symbol:="S", composed:= conductance0.composed}

def mag_flux0 := e_potential * time

def mag_flux: Quality := {name:="Magnetic Flux", short:="magnetic flux", unit:="weber", unit_symbol:="Wb", composed:= mag_flux0.composed}

def mag_flux_dens0 := mag_flux / area

def mag_flux_dens: Quality := {name:="Magnetic Flux Density", short:="magnetic flux density", unit:="tesla", unit_symbol:="T", composed:= mag_flux_dens0.composed}

def inductance0 := mag_flux / e_current

def inductance: Quality := {name:="Inductance", short:="inductance", unit:="henry", unit_symbol:="H", composed:= inductance0.composed}

def lum_flux0 := lum_intensity * s_angle

def lum_flux: Quality := {name:="Luminous Flux", short:="luminous flux", unit:="lumen", unit_symbol:="lm", composed:= lum_flux0.composed}

def illuminance0 := lum_intensity * s_angle  / area

def illuminance: Quality := {name:="Luminous Flux", short:="luminous flux", unit:="lumen", unit_symbol:="lm", composed:= illuminance0.composed}


def decay0 := scalar / time

def decay: Quality := {name:="Decays per Time", short:="decay", unit:="becquerel", unit_symbol:="Bq", composed:= decay0.composed}


def ab_dose0 := area / (time * time)

def ab_dose: Quality := {name:="Absorbed Dose", short:="absorbed dose", unit:="gray", unit_symbol:="Gy", composed:= ab_dose0.composed}

def eq_dose0 := area / (time * time)

def eq_dose: Quality := {name:="Equivalent Dose", short:="equivalent dose", unit:="sievert", unit_symbol:="Sv", composed:= eq_dose0.composed}


def cat_activity0 := am_subst / time

def cat_activity: Quality := {name:="Catalytic Activity", short:="catalytic activity", unit:="katal", unit_symbol:="kat", composed:= cat_activity0.composed}

def lum_efficacy := lum_intensity / power




-- SI is the International system of units
def SI : List Quality := [
  -- basic
  scalar,
  length,
  mass,
  time,
  e_current,
  temp,
  am_subst,
  lum_intensity,
  -- derived
  area,
  volume,
  speed,
  acceleration,
  s_angle,
  p_angle,
  frequency,
  force,
  pressure,
  energy,
  power,
  e_charge,
  e_potential,
  capacitance,
  resistance,
  conductance,
  mag_flux,
  mag_flux_dens,
  inductance,
  lum_flux,
  illuminance,
  decay,
  ab_dose,
  eq_dose,
  cat_activity,

]

#eval SI.map QtoString


-- This will find all qualities that are compatible from the SI
def fromSI (p : Quality): List Quality :=
  List.filter (λ x => equal x p) SI

def set_decimalQ (q:Quality) (d:Int) : Quality :=
  {
    name:=q.name,
    definition:= q.definition,
    short:= q.short,
    unit:= q.unit,
    unit_symbol:= q.unit_symbol,
    composed:=(dict_insert q.composed predecimal d)}

#eval List.map (λ x => QtoString x) (fromSI acceleration0)

structure Measure (α : Type) [ToString α] [Inhabited α] where
  quality: Quality
  quantity: α := default

def set_decimal [Inhabited α] [ToString α] (m: Measure α) (d: Int) : Measure α  :=
  {quantity:=m.quantity, quality:= set_decimalQ m.quality d}

def scalar_dec : Quality := decimal



def non_measure [Inhabited α] [ToString α]: Measure α :=
  { quality := forced, quantity := default }


def add {α : Type} [Inhabited α] [ToString α](m: Measure α ) (n: Measure α ) [HAdd α α α]: Measure α :=
  if equal m.quality n.quality then
    let q:α := m.quantity + n.quantity
    {quality:=m.quality, quantity:= q}
  else
    non_measure


-- Define an instance of HAdd for Measure
-- instance : HAdd  (α : Type)  Measure α Measure Measure :=
-- {
--   hAdd := add
-- }

-- Define an instance of HAdd for Measure
-- instance {α : Type} [Inhabited α] [HAdd α α α] : HAdd (Measure α) (Measure α) (Measure α) :=
-- {
--   hAdd := add α
-- }


def sub {α : Type} [Inhabited α] [ToString α] (m: Measure α ) (n: Measure α ) [HSub α α α]: Measure α :=
  if equal m.quality n.quality then
    let q:α := m.quantity - n.quantity
    {quality:=m.quality, quantity:= q}
  else
    non_measure

def mul {α : Type} [Inhabited α] [ToString α] (m: Measure α ) (n: Measure α ) [HMul α α α]: Measure α :=
  {quality:= {composed:= mergeHashMaps m.quality.composed n.quality.composed,name:= n.quality.name ++ "·" ++ m.quality.name, short:="", unit:="", unit_symbol:=""}, quantity:= n.quantity * m.quantity}

def solve_decimal_to  (m: Measure Float) (d: Int) : Measure Float  :=
  let o_diff := dict_lookup m.quality.composed predecimal
  let di :=
    match o_diff with
    | some v => v   -- If there is a value, return it
    | none => 0
  let diff := d - di
  let scalar_diff := set_decimalQ scalar_dec diff
  let m2: Measure Float := {quality:=scalar_diff, quantity:= (Float.pow 10.0 (Float.ofInt diff))}
  mul m m2

def div {α : Type} [Inhabited α] [ToString α] (m: Measure α ) (n: Measure α ) [HDiv α α α]: Measure α :=
  {quality:= divQ m.quality n.quality, quantity:= n.quantity / m.quantity}

-- Ensure the `ToString` typeclass is available for Measure
instance {α : Type} [ToString α] [Inhabited α] : ToString (Measure α) where
  toString m :=
    let unit := QtoString m.quality
    -- let quantity := m.quantity
    -- m.quantity.toString ++ unit
    unit

-- def toString {α : Type} [Inhabited α] [ToString α] (m : Measure α ): String :=
--   -- let val := α
--   let unit := QtoString m.quality
--   (m.quality.name) ++ ": " ++  m.quantity.toString ++ unit

def m_m1 : Measure Float := {quality:= mass, quantity:= 10.6}

def m_m2 : Measure Float := {quality:= mass, quantity:= 4.16}

def l_m2 : Measure Float := {quality:= length, quantity:= 14.6}

def t_m2 : Measure Float := {quality:= time, quantity:= 4.6}

def c : Measure Float := {quantity:= 299792458.0, quality:=speed}

def freq_Cs : Measure Float := {quantity:= 9192631770.0, quality:=frequency}

def luminous_efficacy_540_THz : Measure Float := {quantity:= 683.0, quality:=lum_efficacy}



def scalar_23 := set_decimalQ scalar_dec 23


def avogadro_n : Measure Float := {quantity:=6.02214076, quality:= (scalar_23 / am_subst)}

def av_no:= solve_decimal_to avogadro_n 20

#eval av_no.quantity
#eval QtoString avogadro_n.quality

def deca : Measure Float := {quantity:= 683.0, quality:=lum_efficacy}



def m_m3 := add m_m1 m_m2

def m_m4 := mul m_m1 m_m2

def v_m5 := div l_m2 t_m2

def m_m6 := add m_m1 l_m2

def u_m5 := div m_m2 m_m2

#eval QtoString m_m3.quality
#eval m_m3.quantity

#check Float.toString 4.5

-- #eval toString c
#eval c
#eval c

#eval QtoString v_m5.quality
#eval v_m5.quantity

#eval QtoString m_m6.quality
#eval m_m6.quantity

#eval QtoString u_m5.quality
#eval u_m5.quantity


def measureDict2 (α : Type) [Inhabited α] [ToString α]: Type :=
  dict String (Measure α)
-- #check measureDict

def measureDict (α : Type) [ToString α] [Inhabited α] := dict String (Measure α)

def constants : measureDict Float := Batteries.HashMap.empty

-- def constants : measureDict Float := Batteries.HashMap.empty
-- empty_dict

dict_insert constants "c" c

#check dict_lookup constants "c"
def f:=dict_lookup constants "c"
#check f.quantity
-- measureDict
