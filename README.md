# idris-learning

В данном репозитории расположенны материалы по изучению языка Idris.
Он не претендует на звание учебника или даже курса по изучению данного языка. 
Но материалы из репозитория могут помочь при прохождении куса от Computer Science клуба 
[Программирование с зависимыми типами на языке Idris | Виталий Брагилевский](https://www.youtube.com/playlist?list=PL-_cKNuVAYAXFRLj6n2nDjI1cyHjuI3HI)

## Структура
* Файл [examples.idr](./examples.idr) - конспект лекций
* Католог [hw10](./hw10/) содержит решения домашней работы № 10 по курсу Теории Ттипо от Д. Г. Штукендерга ITMO ([список заданий](https://github.com/shd/tt2019/blob/master/hw-theory.pdf))

## Как настроить окружение
1. Установить Idris ([скачать](https://www.idris-lang.org/download/))
2. Установить Atom ([скачать](https://atom.io))
   * Установить расширение ([репозиторий расширения](https://atom.io/packages/language-idris)).
     Можно его поставить через сам Atom: File -> Settings -> Install -> Ввести: 'Language Idris' -> Нажать `Install`
   * Установить путь до Idris, если он не в переменной PATH (Проверить можно так: открыть терминал и ввестит команду `idris`).
     File -> Settings -> Packages -> language-idris (Кликнуть не по названию 😉) -> В поле `Idris Location` ввести путь до инерпретатора
3. Открыть папку проекта
