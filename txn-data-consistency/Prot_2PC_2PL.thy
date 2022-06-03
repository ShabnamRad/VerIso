section \<open>Two Phase Commit (2PC) with Two Phase Locking (2PL)\<close>

theory Prot_2PC_2PL
  imports Key_Value_Stores
begin

subsection \<open>2PC Event system\<close>

subsubsection \<open>State\<close>

datatype status_rm = working | prepared | okay | notokay | committed | aborted |
                     prep_uabort | user_aborted
datatype status_tm = tm_init | tm_prepared | tm_committed | tm_aborted | tm_user_aborted

record tm_state =
  tm_status :: status_tm
  tm_tid :: nat

typedecl rmid

record 'v rm_state =
  rm_main_db :: "'v kv_store"
  rm_shadow_db :: "'v kv_store"
  rm_status :: status_rm
  rm_tid :: nat

type_synonym 'v rms_state = "rmid \<Rightarrow> 'v rm_state"

record 'v global_state =
  tm :: tm_state
  rms :: "'v rms_state"


subsubsection \<open>Events\<close>

datatype ev2 = Prepare rmid | OK rmid | NOK rmid | PrepUAbort rmid |
               UAbort rmid | Commit rmid | Abort rmid | Ready rmid |
               User_Commit | User_Abort | TM_Commit | TM_Abort |
               TM_ReadyC | TM_ReadyA | Skip


end