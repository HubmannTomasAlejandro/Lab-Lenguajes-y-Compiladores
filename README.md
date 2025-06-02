# Lab - Lenguajes y Compiladores

A lo largo de este archivo se realiza la implementación del lenguaje de la materia con Haskell, salvo los operadores **para todo** y **existe** para booleanos. El código se divide en varias partes:

## 1. Definición de tipos y sintaxis

En primer lugar, se definen los tipos para `Var`, `Σ` y los dominios semánticos. Luego se especifica la manera en la que se construye la sintaxis de las expresiones de los distintos dominios.

## 2. Funciones auxiliares

A continuación, se presentan las definiciones de funciones auxiliares que se utilizarán para dar la semántica de los distintos dominios. Entre estas se encuentran algunas funciones vistas en la parte teórica, como:

- `resty` y `f_big`, que se usan para que la semántica sea dirigida por la sintaxis.
- `(*.)`, `(†.)` y `(+.)`, que se definen para garantizar la propagación del comportamiento ante errores.

También se incluyen funciones para manejar los problemas de tipos que se presentan al utilizar `MInt` y `MBool` para representar los dominios semánticos de los enteros y booleanos, respectivamente:

- `>>==`
- `-^-`
- `-^`

Finalmente, se define la función `fix`, que se utiliza para obtener el menor punto fijo de una función, y la función `eval`, usada para modificar el estado que recibe la semántica a lo largo de la evaluación.

## 3. Semánticas de los dominios

Luego se encuentran las definiciones de las semánticas de los distintos dominios. Estas incluyen:

- La semántica de expresiones de tipo `MInt` y `MBool`.
- La semántica de expresiones de tipo `Ω`.

## 4. Evaluación y pruebas

Finalmente, se encuentra la definición de `eval` para los distintos dominios semánticos. Esta es una función que recibe una expresión del dominio y un estado, y realiza **acciones observables** (como imprimir valores), sin devolver un resultado útil.

Además, se incluye una **lista de tests** que se utilizan para verificar el correcto funcionamiento de las semánticas.
