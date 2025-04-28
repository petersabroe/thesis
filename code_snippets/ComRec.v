Record raw_com := 
  { Key : choice_type
  ; Value : choice_type
  ; Commitment : choice_type 
  ; Opening : choice_type

  ; setup : 
      code no_locs [interface] Key

  ; commit :
    ∀ (k : Key) (u : Value),
      code no_locs [interface] (Commitment × Opening)

  ; verify :
    ∀ (k : Key) (c : Commitment) (v: Value) (d : Opening),
      code no_locs [interface] bool

  ; sampl_value : 
      code no_locs [interface] Value

  }.
