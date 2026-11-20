# PREREG C21: qué términos de opponent shaping conservan los equilibrios de Nash (resultado de clase)

20/11/2026. Se congela antes de cualquier comprobación numérica o demostración. Línea AA_MIXED_NASH_SCOPE_AUDIT. Sigue a C05–C07 (covarianza, contraejemplo, bienestar frente a incentivos).

## Pregunta

El preprint deja abierta esta pregunta: ¿hay alguna reparación de AA que conserve los equilibrios mixtos sin perder la señal de shaping? La formulamos para una clase general de términos.

## Marco (juego en forma normal, una etapa)

- Dos jugadores, acciones finitas A y B, políticas softmax con interior p (sobre A) y q (sobre B).
- Pagos u₁, u₂: A×B → ℝ. Descomposición ANOVA ponderada por (p, q), como en la Prop. 5 del preprint:
  - jugador 2: u₂ = κ₂ + n₂(a) + s₂(b) + i₂(a,b);
  - jugador 1: u₁ = κ₁ + r₁(a) + t₁(b) + j₁(a,b).
- (p, q) es un equilibrio de Nash interior ⇔ r₁ = 0 y s₂ = 0. Es decir, cada jugador es indiferente entre sus acciones frente a la política del otro. Los juegos con Nash en (p, q) forman el subespacio lineal G = G₁ × G₂, con G₁ = {u₁ : r₁ = 0} y G₂ = {u₂ : s₂ = 0}.
- Término de shaping local del jugador 1: T(u₁, u₂) ∈ ℝ^A, bilineal en (u₁, u₂) para (p, q) fijos. La actualización es θ₁ ← θ₁ + α(∇θ₁V₁ + β T). Como ∇θ₁V₁ = J_p r₁ se anula en Nash, (p, q) sigue siendo punto fijo para todo β ⇔ T = 0 en G.

## Enunciados que se van a demostrar

- **T11 (caracterización).** T se anula en todo juego con Nash interior en (p, q) ⇔ existen B₁ y B₂ bilineales tales que T(u₁, u₂) = B₁(r₁, u₂) + B₂(u₁, s₂). Es decir, T está **controlado por un incentivo**: depende del pago propio solo a través de r₁ o del pago del rival solo a través de s₂.
- **T12 (los casos conocidos).**
  - (a) AA (C05) no está controlado por un incentivo: lee n₂ con peso W, que depende de la ventaja conjunta pasada.
  - (b) LOLA de primer orden no lo está: J_p i₂ J_q g, con g = ∇θ₂V₁ = J_q t₁, es decir, lee i₂ y t₁.
  - (c) LookAhead (LOLA sin χ) sí lo está, a través de s₂.
  - (d) AA con el peso pasado marginalizado (Prop. 7 del preprint) sí lo está, a través de r₁.
- **T13 (no hay shaping gratis).** Si T conserva todos los Nash interiores, entonces T ≡ 0 en G. Su efecto en el equilibrio se limita a la derivada: puede cambiar la estabilidad local (como SOS), pero no la posición de ningún equilibrio. Todo término que actúe en el equilibrio leyendo bienestar (n₂), interacción (i₂) o el efecto del rival sobre mí (t₁) desplaza algún Nash.

## Predicciones numéricas (antes de demostrar)

- **P1.** Con p y q interiores aleatorios, para 2×2, 3×3 y 3×4 y 2000 juegos en G muestreados al azar: |T| ≤ 1e-12 para LookAhead y para AA con peso marginal. |T| > 1e-6 en al menos el 99% de los juegos para AA y LOLA.
- **P2.** Para formas bilineales aleatorias genéricas, la anulación en G coincide con la factorización de T11. Se comprueba por rango: dimensión del núcleo frente a la dimensión del subespacio controlado.
- **P3.** Desplazamiento: con β pequeño, el nuevo punto fijo de AA está a distancia O(β) del Nash, y el signo de la primera componente coincide con el signo de W·J_p n₂ en el 100% de los casos con |W·J_p n₂| > 1e-3.

## Falsadores

- Cualquier juego en G con |T| > 1e-9 para LookAhead o para AA con peso marginal falsa T12(c, d).
- Un T bilineal que se anule en G y no admita la factorización falsa T11, lo que obligaría a revisar el álgebra.
- Un fallo de P3 en más del 1% de los casos falsa la predicción de signo.

## Alcance y límites (declarados antes)

- Solo una etapa y forma normal. La extensión a juegos de Markov con pesos sobre historias se hará aparte; la Prop. 4 del preprint la sugiere por linealidad.
- Solo términos bilineales. Los términos no lineales en pagos (por ejemplo POLA, M-FOS o métodos con aproximación de primer orden) quedan fuera; se dirá así.
- No se reclama novedad frente a Letcher et al. (2019) en la idea general de que «un ajuste que no se anula en los puntos fijos los desplaza». Lo que se reclama es la caracterización por componentes ANOVA y su corolario para AA y LOLA.
- Es verificación interna (O8): no quita ningún asterisco.

## Plan

1. Congelar este preregistro (commit).
2. Script `formal/c21_shaping_class.py` con P1–P3.
3. Demostración en texto. Formalización en Lean de T11 en dimensión finita, después.
4. Informe `formal/INFORME_C21_CLASE_SHAPING_NASH.md`.
