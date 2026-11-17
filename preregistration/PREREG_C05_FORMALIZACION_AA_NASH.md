# PREREG C05 — Verificación formal (Lean 4 + Mathlib) del contraejemplo AA/Nash y su caracterización

17/11/2026. Claude, ciclo 5. Línea AA_MIXED_NASH_SCOPE_AUDIT (CT2 80, rama distinta de la
institucional). Enunciados fijados ANTES de escribir ninguna demostración en Lean. Fuente
matemática: `v19_voluntary_exchange/V205_NASH_COUNTEREXAMPLE_NOTE.md` (V205) y la ecuación 8
de Duque et al., *Advantage Alignment Algorithms*, ICLR 2025.

## Por qué

La puerta pendiente de esta línea es la confirmación independiente. Para un resultado
matemático, un verificador de demostraciones (el núcleo de Lean) es un comprobador independiente
del razonamiento y del código del proyecto: no comparte el simulador, ni SymPy, ni JavaScript.
No sustituye la revisión por pares ni establece prioridad.

## Teoremas a formalizar

Notación: acciones finitas, políticas softmax/Bernoulli-logit independientes, ventajas
fijadas (detached), W peso previo a la acción.

- **T1 (identidad del score).** Para una softmax sobre un tipo finito, Σₐ π(a)·∇_θ log π(a) = 0.
  Se formaliza al menos el caso Bernoulli-logit (score de la acción ±1 = (±1 − m)/2, con
  m = 2σ(θ) − 1) y, si es factible, el caso softmax general.
- **T2 (caracterización por covarianza).** Para πᵢ, πⱼ independientes y cualesquiera A : Aᵢ×Aⱼ → ℝ
  y S : Aᵢ → ℝ con Σ πᵢ S = 0:
  Σ_{aᵢ,aⱼ} πᵢ(aᵢ) πⱼ(aⱼ) W A(aᵢ,aⱼ) S(aᵢ) = W · Σ_{aᵢ} πᵢ(aᵢ) S(aᵢ) (μ(aᵢ) − μ̄),
  con μ(aᵢ) = Σ_{aⱼ} πⱼ(aⱼ) A(aᵢ,aⱼ), es decir W · Cov_{πᵢ}(S, μ).
- **T3 (corrección marginal).** Sustituir A por Ā(aⱼ) = Σ_{aᵢ} πᵢ(aᵢ) A(aᵢ,aⱼ) anula el término
  para cualquier política: Σ πᵢ πⱼ W Ā(aⱼ) S(aᵢ) = 0.
- **T4 (juego del contraejemplo).** En el juego de dos etapas de V205 (acciones con signo ±1,
  recompensas z(1+cx), −cxz; cfg, f(z−cg); 0<γ, c>0), con el perfil uniforme π*:
  - T4a: los valores de estado son 0 y las ventajas conjuntas exactas son las recompensas
    de cada etapa;
  - T4b: ninguna desviación unilateral determinista dependiente de la historia mejora el
    retorno 0 de ninguno de los jugadores (luego π* es Nash);
  - T4c: el campo de la ecuación 8 es F₁ = (0, βγ³/4, βγ³/4) y F₂ = 0 (suma exacta sobre las
    16 trayectorias, con el gradiente privado incluido);
  - T4d: tras θ' = θ* + αF con α, β > 0, el jugador 2 tiene una desviación con retorno
    γ(1+c)·m > 0, donde m = 2σ(αβγ³/4) − 1 > 0, mientras su retorno en la política es 0.
    Luego θ' no es Nash.
- **T5 (no-preservación genérica).** Corolario de T2: en un perfil interior con Wᵢ ≠ 0, el
  término de alineamiento es nulo si y solo si Cov_{πᵢ}(Sᵢ, μⱼ) = 0. En T4 la covarianza es
  positiva.

## Criterios

Éxito: todos los teoremas compilan en Lean sin `sorry`, `admit` ni axiomas añadidos (se
comprueba con `#print axioms`, que solo puede mostrar propext, Classical.choice y Quot.sound).
Si un enunciado resulta falso o mal planteado, se registra como errata con el contraejemplo
encontrado y no se reformula en silencio. T1 general y T5 en su forma «si y solo si» son
deseables; T2, T3 y T4 son el núcleo.

## Lo que no cambia

No se contacta a los autores (decisión del usuario). La prioridad se revisa por separado:
versiones posteriores del artículo (arXiv), literatura de opponent shaping (Letcher et al.
2019 sobre SOS, LOLA, POLA, COLA) y búsquedas registradas. CT2 y N2 solo se revisan tras esa
revisión.
