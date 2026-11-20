# PREREG C21b: el shaping desplaza al rival, no a quien da forma

20/11/2026. Se congela antes de ejecutar ninguna comprobación de C21b. Viene del hallazgo exploratorio de C21 (informe `INFORME_C21_CLASE_SHAPING_NASH.md`, commit `56e0d00`): en 486 juegos 2×2, quien daba forma no se movía (mediana 1,1·10⁻¹⁶) y el rival se movía O(β), con el signo de −βH₁₂⁻¹T en el 100% de los casos. Ese dato **no** cuenta como confirmación. Aquí se usan semillas, tamaños y términos nuevos.

## Teoría (escrita antes de comprobar)

- Juego en forma normal de una etapa, políticas softmax y Nash interior (p, q).
- Campo del jugador 1: F₁ = J_p u₁ q + β T(p,q). Campo del jugador 2: F₂ = J_q u₂ᵀ p, que es ingenuo, sin shaping.
- **Lema (bloques propios nulos).** En el Nash interior, u₁q = c·**1**. Como J_p **1** = 0 para todo p, ∂F₁/∂θ₁ = 0 cuando β = 0. Lo mismo vale para el jugador 2. El jacobiano del campo ingenuo es [[0, H₁₂], [H₂₁, 0]], con H₁₂ = J_p u₁ J_q y H₂₁ = J_q u₂ᵀ J_p, en coordenadas logit reducidas.
- **Primer orden.** El nuevo punto fijo cumple H₂₁ δ₁ = O(β²) y H₁₂ δ₂ = −β T + O(β²). Si |A| = |B| y H₁₂, H₂₁ son invertibles:
  - δ₁ = O(β²): quien da forma no se mueve a primer orden;
  - δ₂ = −β H₁₂⁻¹ T + O(β²): se mueve el rival.

## Hipótesis y criterios

Términos de shaping: AA (como en C21) y LOLA de primer orden. Se usan juegos con Nash interior en (p, q) muestreados como en C21, con la semilla nueva 20261122.

- **H1 (juegos cuadrados, 2×2, 3×3 y 4×4; 500 juegos por tamaño y término).** Con β = 10⁻³ y β = 5·10⁻⁴, en los juegos donde Newton converge (|F| < 1e-10):
  - (a) ‖δ₁‖/‖δ₂‖ < 10⁻² en al menos el 99% de los juegos;
  - (b) error relativo ‖δ₂ − (−β H₁₂⁻¹ T)‖/‖δ₂‖ < 5·10⁻² en al menos el 99%;
  - (c) al pasar de β a β/2, ‖δ₂‖ se reduce a la mitad (cociente entre 1,8 y 2,2) y ‖δ₁‖ a la cuarta parte o menos (cociente ≥ 3), en al menos el 95%.
  - Se excluyen y se cuentan los juegos con cond(H₁₂) > 10⁶ o en los que Newton no converge. Si se excluye más del 10%, H1 queda NO CONCLUYENTE.
- **H2 (el que da forma tiene menos acciones: 2×3 y 3×4).** H₂₁ tiene columnas independientes en general, así que δ₁ = O(β²). Se predice ‖δ₁‖/‖δ₂‖ < 10⁻² en al menos el 95%. El punto fijo se calcula con Gauss-Newton de norma mínima, porque los equilibrios del rival forman un continuo.
- **H3 (el que da forma tiene más acciones: 3×2 y 4×3). EXPLORATORIA, sin predicción.** El sistema H₁₂ δ₂ = −βT está sobredeterminado. Se registrará si existe un punto fijo cercano (con Gauss-Newton), la proporción ‖δ₁‖/‖δ₂‖ y si ‖δ₁‖ escala como β o como β².

## Falsadores

- Si H1(a), (b) o (c) fallan por debajo de los umbrales, el resultado exploratorio de C21 queda refutado o acotado a 2×2.
- Si en H2 ‖δ₁‖/‖δ₂‖ ≥ 10⁻² en más del 5% de los juegos, falla la extensión a |A| < |B|.

## Alcance

- Una sola etapa, Nash interior, solo shaping del jugador 1 y rival ingenuo. El caso con shaping simultáneo de los dos jugadores queda fuera.
- No se reclama la idea general de «moverse para que el otro se mueva» frente a la literatura sobre Stackelberg o liderazgo. Lo que se contrasta es la predicción concreta de primer orden en equilibrios mixtos.
- Es evidencia interna (O8).

## Plan

1. Congelar (commit).
2. Escribir `formal/c21b_rival_shift.py` y ejecutarlo; resultados en `formal/C21_RESULTS/c21b_results.json`.
3. Informe `formal/INFORME_C21B_DESPLAZAMIENTO_DEL_RIVAL.md`.
