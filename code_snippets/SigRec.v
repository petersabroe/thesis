Record raw_sigma :=
  { Statement : choice_type
  ; Witness : choice_type
  ; Message : choice_type
  ; State : choice_type
  ; Challenge : choice_type
  ; Response : choice_type

  ; R : Statement → Witness → bool

  ; commit :
    ∀ (h : Statement) (w : Witness),
      code no_locs [interface] (Message × State)

  ; response :
    ∀ (h : Statement) (w : Witness)
      (a : Message) (s : State) (e : Challenge),
      code no_locs [interface] Response

  ; verify :
    ∀ (h : Statement) (a : Message) (e : Challenge)
      (z : Response),
      bool

  ; simulate :
    ∀ (h : Statement) (e : Challenge),
      code no_locs [interface] (Message × Response)

  ; extractor :
    ∀ (h : Statement) (a : Message)
      (e : Challenge) (e' : Challenge)
      (z : Response) (z' : Response),
      'option Witness
  }.