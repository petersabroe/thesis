Definition Call_correct_sig (p: raw_sigExt) :
  module (ICorrect p) (ICorrect_com (sig_to_com p)) := 
  [module no_locs ;
      #def #[ CORRECTNESS ] (v : 'value (sig_to_com p)) : 'bool
          {
            #import {sig #[ RUN ] : ('input p) → 'bool} as COR ;;
            '(w, h) ← p.(key_gen);;
            b ← COR (h, w, v) ;;
            ret b
          }
  ].