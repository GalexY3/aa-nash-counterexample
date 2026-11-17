# PREREG C06 — Moldeo por bienestar frente a moldeo por incentivos (AA frente a LOLA)

17/11/2026. Enunciados fijados antes de escribir demostraciones en Lean. Motivación: C05
mostró que AA no es invariante a la equivalencia estratégica. Hipótesis: los métodos de
opponent shaping se distinguen por QUÉ componente del pago del rival leen.

## Descomposición

Juego en un estado con acciones finitas, políticas independientes p (propia) y q (rival).
Pago del rival u₂(a,b) = c + n₂(a) + s₂(b) + i₂(a,b), con E_p n₂ = 0, E_q s₂ = 0,
E_q i₂(a,·) = 0 para todo a y E_p i₂(·,b) = 0 para todo b (ANOVA ponderada por las políticas).
- n₂: efecto de MI acción en el bienestar del rival (no estratégico para el rival).
- s₂: efecto de su propia acción.
- i₂: interacción, es decir, cómo mi acción cambia los incentivos del rival.
J_p = diag(p) − p pᵀ es el jacobiano de softmax (resultado estándar, no formalizado).

## Teoremas

- **T8 (AA lee solo n₂).** El término de alineamiento por estado,
  W·Σ_{a,b} p(a)q(b)(u₂(a,b) − V₂)S(a), con S(a) = e_a − p, no cambia al sumar cualquier s₂(b)
  ni cualquier i₂ centrada en b bajo q. Al sumar n₂(a) cambia en W·Σ_a p(a) n₂(a) S(a) = W·J_p n₂.
- **T9 (LOLA lee solo i₂).** El término de moldeo de LOLA de primer orden, J_p u₂ J_q g (g el
  gradiente de mi valor respecto a los logits del rival), no cambia al sumar n₂(a) ni s₂(b), y
  al sumar i₂ cambia en J_p i₂ J_q g.
- **T10 (separación).** Existen juegos 2×2 en el perfil uniforme en los que (i) el término de AA
  es no nulo y el de LOLA nulo (juego de «regalo», i₂ = 0) y (ii) el de LOLA no nulo y el de AA
  nulo (juego de «incentivo», n₂ = 0).

Criterio: compilación en Lean sin sorry ni axiomas añadidos. Falsador: no poder demostrarlos o
encontrar contraejemplos. La lectura sociológica (reciprocidad o altruismo condicional frente
a sanción o diseño de incentivos) es interpretación, no teorema.

Antecedentes revisados en el scout (claude_cycle04/novelty, search_log_C06): Candogan et al.
2011 (descomposición de juegos); Letcher et al. 2019 y Balduzzi et al. 2018 (descomposición
del jacobiano del juego en partes simétrica y antisimétrica, que es otra cosa); Ramponi y
Restelli 2021 (Helmholtz); Lin et al. 2026 («The Reciprocity Gradient», reputación, no esta
descomposición). No se ha encontrado esta caracterización. Novedad no establecida.
