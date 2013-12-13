package at.logic.utils

/**
 * Created with IntelliJ IDEA.
 * User: marty
 * Date: 10/30/13
 * Time: 7:26 PM
 * To change this template use File | Settings | File Templates.
 */
package object latex {
  // Add more unicode symbols if necessary
  def nameToLatexString(name: String) = name match {
    case "~" => """ \sim """
    case "∈" => """ \in """
    case "ν" => """ \nu """
    case "⊆" => """ \subseteq """
    case "∪" => """ \cup """
    case "∩" => """ \cap """
    case "≤" => """ \leq """
    case "<=" => """ \leq """
    case ">=" => """ \geq """
    case "Α" => """ A """
    case "Β" => """ B """
    case "Γ" => """ \Gamma """
    case "Δ" => """ \Delta """
    case "Ε" => """ E """
    case "Ζ" => """ Z """
    case "Η" => """ H """
    case "Θ" => """ \Theta """
    case "Ι" => """ I """
    case "Κ" => """ K """
    case "Λ" => """ \Lambda """
    case "Μ" => """ M """
    case "Ν" => """ N """
    case "Ξ" => """ \Xi """
    case "Ο" => """ O """
    case "Π" => """ \Pi """
    case "Ρ" => """ \Rho """
    case "Σ" => """ \Sigma """
    case "Τ" => """ T """
    case "Υ" => """ \Upsilon """
    case "Φ" => """ \Phi """
    case "Χ" => """ \Chi """
    case "Ψ" => """ \Psi """
    case "Ω" => """ \Omega """
    case "α" => """ \alpha """
    case "α_0" => """ \alpha_0 """
    case "α_1" => """ \alpha_1 """
    case "α_2" => """ \alpha_2 """
    case "α_3" => """ \alpha_3 """
    case "α_4" => """ \alpha_4 """
    case "α_5" => """ \alpha_5 """
    case "α_6" => """ \alpha_6 """
    case "α_7" => """ \alpha_7 """
    case "α_8" => """ \alpha_8 """
    case "α_9" => """ \alpha_9 """
    case "β" => """ \beta """
    case "γ" => """ \gamma """
    case "δ" => """ \delta """
    case "ε" => """ \epsilon """
    case "ζ" => """ \zeta """
    case "η" => """ \eta """
    case "θ" => """ \theta """
    case "ι" => """ i """
    case "κ" => """ \kappa """
    case "λ" => """ \lambda """
    case "μ" => """ \mu """
    case "ν" => """ \nu """
    case "ξ" => """ \xi """
    case "ο" => """ o """
    case "π" => """ \pi """
    case "ρ" => """ \rho """
//    case "ς" => """\sigma"""
    case "σ" => """ \sigma """
    case "τ" => """ \tau """
    case "υ" => " \\upsilon "
    case "φ" => """ \varphi """
    case "χ" => """ \chi """
    case "ψ" => """ \psi """
    case "ω" => """ \omega """
    case "∈" => """ \in """
    case "⊥" => """ \bot """
    case "⊤" => """ \top """ 
    case _ => //if (!name.matches("""[\w]*|[+]|[=]|[*]|[<]|[>]""")) println(name)
      name
  }

}
