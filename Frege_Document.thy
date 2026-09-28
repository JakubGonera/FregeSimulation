theory Frege_Document
  imports Reckhow
begin

section \<open>Main theorem\<close>

text \<open>
  The main result states that any two systems satisfying the formalized
  Frege-system conditions admit a simulation with polynomially bounded
  proof size. The definitions and the complete proof are in the imported
  theories.
\<close>

theorem frege_systems_simulate:
  assumes "frege_system F1" and "frege_system F2"
  shows "simulates F1 F2"
  using assms Reckhow by blast

end
