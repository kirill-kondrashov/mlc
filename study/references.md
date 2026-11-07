# Источники для B3

## Ближайшие результаты и проверка вклада

- Bonnot–Braverman–Yampolsky,
  [*Thurston equivalence to a rational map is decidable*, 2010v1](https://arxiv.org/abs/1009.5713v1),
  §2, с. 3–4 препринта: наша карта и известный инвариантный экватор.
  Нужны для исходной разметки и проверки вычисленного подъёма.
- Bartholdi–Dudko–Pilgrim,
  [*Correspondences on Riemann surfaces and non-uniform hyperbolicity*, 2025v2](https://arxiv.org/abs/2407.15548v2),
  Corollary B, §1.1: аттракторы при четырёх посткритических точках;
  §1.3: стратегия для большего числа точек. Для вычислений нужны
  §§2.5, 5.1 о бисетах. Готовый вывод для B3 из этих мест не получен.
- Wu,
  [*On the Global Curve Attractor for polynomial gluing*, 2026v2](https://arxiv.org/abs/2605.00633v2),
  Main Theorem и §§2.2–2.3: склейка двух полиномов по конечным бассейнам.
  Неприменимость к B3 и всем её итерациям доказана
  [через локальные степени](research/B3_candidate.md).
- Pilgrim,
  [*An algebraic formulation of Thurston's characterization of rational functions*](https://www.numdam.org/article/AFST_2012_6_21_S5_1033_0.pdf),
  Theorem 1.4, печатная с. 1039; §§5, 7: виртуальный эндоморфизм
  группы классов отображений и критерий конечного аттрактора.
  **Применимость к нашей карте ещё нужно проверить.**
- Pilgrim,
  [*On the pullback relation on curves induced by a Thurston map*, 2021v1](https://arxiv.org/abs/2102.12402v1),
  §§3.3, 4.1: вычисление отношения и перечень известных механизмов.
  Используется как карта ссылок к первичным теоремам.

## Для ближайшего вычисления

- Bartholdi–Dudko I,
  [§2](https://arxiv.org/abs/1512.08539): левосвободный бисет, базис,
  рекурсия и смена базиса. Применение — получить слова секций в (C5).
- Bartholdi–Dudko II,
  [§§2, 3.1, 6](https://arxiv.org/abs/1603.04059): сферические бисеты,
  мультикривые и группы классов отображений. Применение — сохранить
  периферические классы и согласовать подъёмы кривых.
- Farb–Margalit,
  [*A Primer on Mapping Class Groups*](https://doi.org/10.23943/princeton/9780691147949.001.0001),
  §1.2 и §§3.1–3.2: простые кривые, твисты Дена и числа пересечений.
  Нужны определения и доказательства, используемые при расчёте
  семейства с произвольным числом твистов.

Любич, [книга](https://www.math.stonybrook.edu/~mlyubich/book.pdf),
используется для конкретного аналитического перехода, если он понадобится.
Местная версия — `refs/Lyubich_book_vol_I-II_2023.pdf`.
Михайлов–Пасси,
[*Lower Central and Dimension Series of Groups*](https://link.springer.com/book/10.1007/978-3-540-85818-8),
сохраняется как источник по коммутаторам и факторам для прежнего направления.

## Завершённые сравнения

- [B1-R](research/B1_novelty_audit.md), [B2-N](research/B2_novelty_audit.md):
  *p-Basilica Groups*, Lemma 3.2, Theorems 3.3, 4.7(i), 4.10(i),
  Corollary 4.11; ссылки и точные сведения сохранены в аудитах.
- [Карта предшественников B1/B2](research/B1_prior_art.md).
- [Общая библиотека проекта](../refs/README.md).
