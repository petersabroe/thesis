Definition Special_Soundness_t p :
  game (Soundness p) :=
  [module no_locs ;
    #def #[ SOUNDNESS ] ('((h, a), ((e, z), (e', z'))) : 'soundness p) : 'bool {
      let b := p.(verify) h a e z in
      let b' :=  p.(verify) h a e' z' in
      let b'' := (e != e') in 
      @ret 'bool (b && b' && b'')
    }
  ].

Definition Special_Soundness_f p :
  game (Soundness p) :=
  [module no_locs ;
    #def #[ SOUNDNESS ] ('((h, a), ((e, z), (e', z'))) : 'soundness p) : 'bool {
      let b := p.(verify) h a e z in
      let b' :=  p.(verify) h a e' z' in
      let b'' := (e != e') in 
      let ow := p.(extractor) h a e e' z z' in
      @ret 'bool (if ow is Some w then ((p.(R) h w) && b && b' && b'') else false)
    }
  ].