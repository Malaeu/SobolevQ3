/-
  Sobolev-NS: Navier-Stokes Regularity via Spectral Gaps
  Main module file

  Extension of Sobolev-Q3 from arithmetic to fluid dynamics.

  ═══════════════════════════════════════════════════════════
  ║  NAVIER-STOKES GLOBAL REGULARITY                       ║
  ║  Domain: 𝕋³ (3D periodic torus)                        ║
  ║  Drift: Viscous dissipation νΔu                        ║
  ║  Noise: Convective cascade (u·∇)u                      ║
  ║  Goal: ε(t) < ∞ ⟹ No blowup                          ║
  ═══════════════════════════════════════════════════════════

  Core principle: DRIFT > NOISE (same as TPC/Goldbach!)
-/

import SobolevNS.NSBasic
import SobolevNS.NSEquation
import SobolevNS.GlobalRegularity
