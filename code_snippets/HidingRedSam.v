Definition Call_SHVZK_sam (p: raw_sigExt) :
  module (Transcript p) (ICommitment (sig_to_com p)) := 
  [module no_locs ;
      #def #[ COMMITMENT ] (v : 'value (sig_to_com p)) : ('commitment (sig_to_com p))
          {
            #import {sig #[ TRANSCRIPT ] : ('input p) → 'transcript p} as TRANS ;;
(*             w ← p.(sampl_wit) ;;  *)
            '(w, h) ← p.(key_gen) ;;
(*             #assert p.(R) h w ;; *)
            u ← (sig_to_com p).(sampl_value) ;;
            '(h, a, e, z) ← TRANS (h, w, u) ;;           
            ret (a : (sig_to_com p).(Commitment))  
            
          }
  ].