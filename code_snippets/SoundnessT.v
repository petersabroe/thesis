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