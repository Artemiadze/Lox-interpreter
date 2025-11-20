use crate::{
    lexing::{Token, TokenKind},
    Lexer,
};
use miette::{Error, LabeledSpan, WrapErr};
use std::{borrow::Cow, fmt};

pub struct Parser<'de> {
    whole: &'de str,
    lexer: Lexer<'de>,
}

impl<'de> Parser<'de> {
    /// Создает новый экземпляр [`Parser`] из заданной входной строки.
    ///
    /// Синтаксический анализатор владеет ссылкой на полный ввод (`whole`) и поддерживает
    /// внутренний экземпляр [`Lexer`], используемый для маркировки исходного кода.
    ///
    /// # Параметры
    ///
    /// * `input` – исходный код для синтаксического анализа.
    ///
    /// # Примеры
    ///
    /// ```
    /// let mut parser = Синтаксический анализатор::new("1 + 2");
    /// let tree = синтаксический анализатор.синтаксическое_выражение();
    /// ```
    pub fn new(input: &'de str) -> Self {
        Self {
            whole: input,
            lexer: Lexer::new(input),
        }
    }

    /// Анализирует полное выражение, используя правила приоритета в стиле Пратта.
    ///
    /// Эта функция является отправной точкой для синтаксического анализа таких выражений, как:
    ///
    /// * арифметические выражения  
    /// * вызовы функций  
    /// * доступ к элементам  
    /// * литералы  
    ///
    /// Весь ввод обрабатывается как одно выражение.
    ///
    /// # Ошибки
    ///
    /// Возвращает [`Error`], если лексический анализатор обнаруживает недопустимый синтаксис или неожиданный токен.
    pub fn parse_expression(mut self) -> Result<TokenTree<'de>, Error> {
        self.parse_expression_within(0)
    }

    /// Анализирует полный * оператор* вместо простого выражения.
    ///
    /// Оператор может содержать:
    ///
    /// * объявления  
    /// * конструкции потока управления  
    /// * блоки  
    /// * операторы выражения  
    ///
    /// Это общая точка входа для синтаксического анализа программы или конструкции верхнего уровня.
    ///
    /// # Todo
    ///
    /// В настоящее время выполняется синтаксический анализ ** одного** оператора;
    ///  в будущих версиях будет выполняться последовательный анализ многих
    /// операторов.
    pub fn parse(mut self) -> Result<TokenTree<'de>, Error> {
        // TODO: in a loop
        self.parse_statement_within(0)
    }

    // Анализирует блок кода, разделенный символами `{` и `}`.
    ///
    /// Функция использует открывающий символ `{`, анализирует тело блока как
    /// оператор и, наконец, ожидает завершающий символ `}`.
    ///
    /// # Примечания
    ///
    /// * В настоящее время в блоке разрешен только один оператор.
    /// * Будущие расширения могут поддерживать списки, разделенные точкой с запятой, или тела в стиле классов.
    ///
    /// # Ошибки
    ///
    /// Возвращает [`Error`], если:
    ///
    /// * `{` или `}` отсутствует,
    /// * внутренний оператор не удается разобрать.
    pub fn parse_block(&mut self) -> Result<TokenTree<'de>, Error> {
        self.lexer.expect(TokenKind::LeftBrace, "missing {")?;
        // TODO: in a loop with semicolons? depends on class vs body
        let block = self.parse_statement_within(0)?;
        self.lexer.expect(TokenKind::RightBrace, "missing }")?;

        Ok(block)
    }

    /// Анализирует список аргументов при вызове функции.
    ///
    /// Этот метод предполагает, что вызывающий объект уже использовал открывающий `(`.
    ///
    /// Он анализирует ноль или более аргументов, разделенных запятыми, и завершает работу, когда
    /// встречает закрывающий `)`.
    ///
    /// # Поведение
    ///
    /// * `()` → пустой список аргументов  
    /// * `(a, b, c)` → три обработанных выражения  
    ///
    /// Каждый аргумент обрабатывается с использованием `parse_expression_within(0)`, чтобы разрешить вложенные
    /// операторы и вызовы функций.
    ///
    /// # Контекст ошибки
    ///
    /// Каждый аргумент заключен в контекст, такой как  
    /// `"в аргументе #2 вызова функции"`  
    /// для обеспечения более полезной диагностики (Miette).
    ///
    /// # Возвращает
    ///
    /// Вектор проанализированного аргумента [`TokenTree`].
    ///
    /// # Ошибки
    ///
    /// * Неожиданные токены в списке аргументов  
    /// * Отсутствует `)`  
    /// * Недопустимое выражение внутри аргумента  
    pub fn parse_fun_call_arguments(&mut self) -> Result<Vec<TokenTree<'de>>, Error> {
        let mut arguments = Vec::new();

        // parent has already eaten left paren as the operator

        if matches!(
            self.lexer.peek(),
            Some(Ok(Token {
                kind: TokenKind::RightParen,
                ..
            }))
        ) {
            // immediate argument list end
        } else {
            loop {
                let argument = self.parse_expression_within(0).wrap_err_with(|| {
                    format!("in argument #{} of function call", arguments.len() + 1)
                })?;
                arguments.push(argument);

                let token = self
                    .lexer
                    .expect_where(
                        |token| matches!(token.kind, TokenKind::RightParen | TokenKind::Comma),
                        "continuing argument list",
                    )
                    .wrap_err("in argument list of function call")?;

                if token.kind == TokenKind::RightParen {
                    break;
                }
            }
        }

        Ok(arguments)
    }

    /// Разбирает *оператор* или *выражение*, используя Pratt-парсер и учитывая
    /// минимальную силу связывания (`min_bp`).
    ///
    /// Этот метод — центральная часть синтаксического анализатора.
    /// Он умеет разбирать:
    /// - произвольные выражения  
    /// - объявления переменных (`var x = ...`)  
    /// - присваивания  
    /// - управляющие конструкции (`if`, `while`, `for`)  
    /// - объявления функций (`fun name(params) { ... }`)  
    /// - объявления классов (`class Name { ... }`)  
    /// - унарные префиксные операторы (`print expr`, `return expr`)  
    /// - круглые скобки `( ... )`  
    /// - вызовы функций (`f(x, y)`)  
    /// - доступ к полям (`object.field`)  
    ///
    /// # Параметры
    /// * `min_bp` — минимальная сила связывания оператора, необходимая для того,
    ///   чтобы продолжить разбор правой части выражения. Используется для
    ///   реализации приоритетов операторов.
    ///
    /// # Возвращаемое значение
    /// Возвращает [`TokenTree`] — абстрактное синтаксическое дерево (AST)
    /// разобранного оператора или выражения.  
    /// Если входные токены закончились — возвращает [`TokenTree::Atom(Atom::Nil)`].
    ///
    /// # Обработка ошибок
    /// При ошибках выбрасываются подробные [`miette::Error`] с подсветкой участка
    /// текста и пояснениями.  
    /// Вложенные вызовы (`parse_expression_within`, `parse_block` и др.)
    /// добавляют контекст с помощью `wrap_err` и `wrap_err_with`.
    ///
    /// # Общее описание алгоритма
    ///
    /// ## 1. Разбор *левой части* (prefix position)
    /// На этом шаге метод читает следующий токен и интерпретирует его как начало
    /// выражения. Поддерживаются:
    /// - идентификаторы (`foo`)  
    /// - ключевые слова (`this`, `super`, `nil`)  
    /// - скобочные выражения `(expr)`  
    /// - префиксные операторы (`return expr`, `print expr`)  
    /// - объявление переменной (`var x = expr`)  
    /// - объявление функции (`fun f(params) { ... }`)  
    /// - объявление класса (`class Name { ... }`)  
    /// - управляющие конструкции (`if`, `for`, `while`)  
    ///
    /// Некоторые конструкции завершают разбор сразу (например, `for`, `if`,
    /// объявления), возвращая готовый узел AST.
    ///
    /// Остальные — создают начальное значение `lhs`, которое далее будет расширяться.
    ///
    /// ## 2. Цикл разбора операторов (postfix и infix)
    /// После первичного `lhs` метод проверяет следующий токен:
    ///
    /// Поддерживаются *постфиксные* операторы:
    /// - вызов функции: `lhs(...)`
    /// - доступ к полю: `lhs.field`
    ///
    /// Поддерживаются *инфиксные* операторы:
    /// - любые операторы, определённые в `infix_binding_power`
    ///
    /// Алгоритм:
    /// - если сила связывания оператора меньше `min_bp` — разбор завершается  
    /// - иначе оператор «присоединяется» к текущему `lhs`
    /// - затем рекурсивно разбирается правая часть с приоритетом `r_bp`
    ///
    /// Таким образом реализуются корректные приоритеты и ассоциативность операторов.
    ///
    /// ## 3. Завершение
    /// Когда нет подходящих операторов, метод возвращает построенное AST.
    ///
    /// # Примечания по грамматике
    ///
    /// Метод реализует логику, близкую к:
    ///
    /// ```text
    /// expression := prefix_expr (postfix_op | infix_op expression)*
    ///
    /// statement  := expression
    ///             | var_declaration
    ///             | fun_declaration
    ///             | class_declaration
    ///             | if_statement
    ///             | while_statement
    ///             | for_statement
    /// ```
    ///
    /// # Примеры
    ///
    /// ```text
    /// Вход:   var x = 1 + 2 * 3;
    /// Выход:  Cons(Var, [Ident("x"), Cons(Add, [1, Cons(Mul, [2, 3])])])
    ///
    /// Вход:   if (x > 0) { print x; } else { print -x; }
    /// Выход:  If { condition: ..., yes: ..., no: ... }
    /// ```
    pub fn parse_statement_within(&mut self, min_bp: u8) -> Result<TokenTree<'de>, Error> {
        let lhs = match self.lexer.next() {
            Some(Ok(token)) => token,
            None => return Ok(TokenTree::Atom(Atom::Nil)),
            Some(Err(e)) => {
                return Err(e).wrap_err("on the left-hand side");
            }
        };

        let mut lhs = match lhs {
            Token {
                kind: TokenKind::Ident,
                origin,
                ..
            } => TokenTree::Atom(Atom::Ident(origin)),

            Token {
                kind: TokenKind::Super,
                ..
            } => TokenTree::Atom(Atom::Super),

            Token {
                kind: TokenKind::This,
                ..
            } => TokenTree::Atom(Atom::This),

            Token {
                kind: TokenKind::LeftParen,
                ..
            } => {
                let lhs = self
                    .parse_expression_within(0)
                    .wrap_err("in bracketed expression")?;

                self.lexer
                    .expect(
                        TokenKind::RightParen,
                        "Unexpected end to bracketed expression",
                    )
                    .wrap_err("after bracketed expression")?;

                TokenTree::Cons(Operator::Group, vec![lhs])
            }

            // unary prefix expressions
            Token {
                kind: TokenKind::Print | TokenKind::Return,
                ..
            } => {
                let op = match lhs.kind {
                    TokenKind::Print => Operator::Print,
                    TokenKind::Return => Operator::Return,
                    _ => unreachable!("by the outer match arm pattern"),
                };
                let ((), r_bp) = prefix_binding_power(op);
                let rhs = self
                    .parse_expression_within(r_bp)
                    .wrap_err_with(|| format!("on the right-hand side of {op:?}"))?;
                return Ok(TokenTree::Cons(op, vec![rhs]));
            }

            Token {
                kind: TokenKind::For,
                ..
            } => {
                self.lexer
                    .expect(TokenKind::LeftParen, "missing (")
                    .wrap_err("in for loop condition")?;

                let init = self
                    .parse_expression_within(0)
                    .wrap_err("in init condition of for loop")?;

                self.lexer
                    .expect(TokenKind::Semicolon, "missing ;")
                    .wrap_err("in for loop condition")?;

                let cond = self
                    .parse_expression_within(0)
                    .wrap_err("in loop condition of for loop")?;

                self.lexer
                    .expect(TokenKind::Semicolon, "missing ;")
                    .wrap_err("in for loop condition")?;

                let inc = self
                    .parse_expression_within(0)
                    .wrap_err("in incremental condition of for loop")?;

                self.lexer
                    .expect(TokenKind::RightParen, "missing )")
                    .wrap_err("in for loop condition")?;

                let block = self.parse_block().wrap_err("in body of for loop")?;

                return Ok(TokenTree::Cons(Operator::For, vec![init, cond, inc, block]));
            }

            Token {
                kind: TokenKind::While,
                ..
            } => {
                self.lexer
                    .expect(TokenKind::LeftParen, "missing (")
                    .wrap_err("in while loop condition")?;

                let cond = self
                    .parse_expression_within(0)
                    .wrap_err("in while loop condition")?;

                self.lexer
                    .expect(TokenKind::RightParen, "missing )")
                    .wrap_err("in while loop condition")?;

                let block = self.parse_block().wrap_err("in body of while loop")?;

                return Ok(TokenTree::Cons(Operator::While, vec![cond, block]));
            }

            Token {
                kind: TokenKind::Class,
                ..
            } => {
                let token = self
                    .lexer
                    .expect(TokenKind::Ident, "expected identifier")
                    .wrap_err("in class name")?;
                assert_eq!(token.kind, TokenKind::Ident);
                let ident = TokenTree::Atom(Atom::Ident(token.origin));

                if lhs.kind == TokenKind::Var {
                    self.lexer
                        .expect(TokenKind::Equal, "missing =")
                        .wrap_err("in variable assignment")?;
                }

                let block = self.parse_block().wrap_err("in class definition")?;

                return Ok(TokenTree::Cons(Operator::Class, vec![ident, block]));
            }

            Token {
                kind: TokenKind::Var,
                ..
            } => {
                let token = self
                    .lexer
                    .expect(TokenKind::Ident, "expected identifier")
                    .wrap_err("in variable assignment")?;
                assert_eq!(token.kind, TokenKind::Ident);
                let ident = TokenTree::Atom(Atom::Ident(token.origin));

                self.lexer
                    .expect(TokenKind::Equal, "missing =")
                    .wrap_err("in variable assignment")?;

                let second = self
                    .parse_expression_within(0)
                    .wrap_err("in variable assignment expression")?;

                return Ok(TokenTree::Cons(Operator::Var, vec![ident, second]));
            }

            Token {
                kind: TokenKind::Fun,
                ..
            } => {
                let token = self
                    .lexer
                    .expect(TokenKind::Ident, "expected identifier")
                    .wrap_err("in function name declaration")?;
                assert_eq!(token.kind, TokenKind::Ident);
                let name = token.origin;
                let ident = Atom::Ident(token.origin);

                let mut parameters = Vec::new();

                self.lexer
                    .expect(TokenKind::LeftParen, "missing (")
                    .wrap_err_with(|| format!("in parameter list of function {name}"))?;

                if matches!(
                    self.lexer.peek(),
                    Some(Ok(Token {
                        kind: TokenKind::RightParen,
                        ..
                    }))
                ) {
                    // immediate parameter list end
                } else {
                    loop {
                        let parameter = self
                            .lexer
                            .expect(TokenKind::Ident, "unexpected token")
                            .wrap_err_with(|| {
                                format!("in parameter #{} of function {name}", parameters.len() + 1)
                            })?;
                        parameters.push(parameter);

                        let token = self
                            .lexer
                            .expect_where(
                                |token| {
                                    matches!(token.kind, TokenKind::RightParen | TokenKind::Comma)
                                },
                                "continuing parameter list",
                            )
                            .wrap_err_with(|| format!("in parameter list of function {name}"))?;

                        if token.kind == TokenKind::RightParen {
                            break;
                        }
                    }
                }

                let block = self
                    .parse_block()
                    .wrap_err_with(|| format!("in body of function {name}"))?;

                return Ok(TokenTree::Fun {
                    name: ident,
                    parameters,
                    body: Box::new(block),
                });
            }

            Token {
                kind: TokenKind::If,
                ..
            } => {
                self.lexer
                    .expect(TokenKind::LeftParen, "missing (")
                    .wrap_err("in if condition")?;

                let cond = self
                    .parse_expression_within(0)
                    .wrap_err("in if loop condition")?;

                self.lexer
                    .expect(TokenKind::RightParen, "missing )")
                    .wrap_err("in if loop condition")?;

                let block = self.parse_block().wrap_err("in body of if")?;

                let mut otherwise = None;
                if matches!(
                    self.lexer.peek(),
                    Some(Ok(Token {
                        kind: TokenKind::Else,
                        ..
                    }))
                ) {
                    self.lexer.next();

                    otherwise = Some(self.parse_block().wrap_err("in body of else")?);
                }

                return Ok(TokenTree::If {
                    condition: Box::new(cond),
                    yes: Box::new(block),
                    no: otherwise.map(Box::new),
                });
            }

            token => {
                return Err(miette::miette! {
                    labels = vec![
                        LabeledSpan::at(token.offset..token.offset + token.origin.len(), "here"),
                    ],
                    help = format!("Unexpected {token:?}"),
                    "Expected a statement",
                }
                .with_source_code(self.whole.to_string()))
            }
        };

        loop {
            let op = self.lexer.peek();
            if op.map_or(false, |op| op.is_err()) {
                return Err(self
                    .lexer
                    .next()
                    .expect("checked Some above")
                    .expect_err("checked Err above"))
                .wrap_err("in place of expected operator");
            }
            let op = match op.map(|res| res.as_ref().expect("handled Err above")) {
                None => break,
                Some(Token {
                    kind: TokenKind::LeftParen,
                    ..
                }) => Operator::Call,
                Some(Token {
                    kind: TokenKind::Dot,
                    ..
                }) => Operator::Field,

                Some(token) => return Err(miette::miette! {
                    labels = vec![
                        LabeledSpan::at(token.offset..token.offset + token.origin.len(), "here"),
                    ],
                    help = format!("Unexpected {token:?}"),
                    "Expected an operator",
                }
                .with_source_code(self.whole.to_string())),
            };

            if let Some((l_bp, ())) = postfix_binding_power(op) {
                if l_bp < min_bp {
                    break;
                }
                self.lexer.next();

                lhs = match op {
                    Operator::Call => TokenTree::Call {
                        callee: Box::new(lhs),
                        arguments: self
                            .parse_fun_call_arguments()
                            .wrap_err("in function call arguments")?,
                    },
                    _ => TokenTree::Cons(op, vec![lhs]),
                };
                continue;
            }

            if let Some((l_bp, r_bp)) = infix_binding_power(op) {
                if l_bp < min_bp {
                    break;
                }
                self.lexer.next();

                let rhs = self
                    .parse_expression_within(r_bp)
                    .wrap_err_with(|| format!("on the right-hand side of {lhs} {op}"))?;
                lhs = TokenTree::Cons(op, vec![lhs, rhs]);
                continue;
            }

            break;
        }

        Ok(lhs)
    }

    /// Разбирает выражение, учитывая минимальную силу связывания (`min_bp`),
    /// реализуя алгоритм Pratt-парсера.
    ///
    /// Это — главный метод разбора *выражений* во всём синтаксическом анализаторе.
    /// Он принимает текущее значение минимального приоритета (`min_bp`) и
    /// последовательно строит дерево выражений с учётом приоритетов и
    /// ассоциативности операторов.
    ///
    ///
    /// # Этапы разбора
    ///
    /// ## 1. Разбор левой части выражения (prefix position)
    /// Сначала метод читает следующий токен и интерпретирует его как начало
    /// выражения. Поддерживаются:
    ///
    /// **Атомы (литералы и идентификаторы):**
    /// - строки  
    /// - числа  
    /// - `true` / `false`  
    /// - `nil`  
    /// - `ident`  
    /// - `this`, `super`  
    ///
    /// **Скобочные выражения:**
    /// - `(expr)` — рекурсивный разбор со сбросом приоритета в 0
    ///
    /// **Унарные префиксные операторы:**
    /// - `-expr`  
    /// - `!expr`  
    ///
    /// Для унарных операторов используется `prefix_binding_power(op)`, чтобы
    /// правильно обработать их силу связывания.
    ///
    /// Если токен не подходит под начало выражения — возвращается подробная
    /// диагностическая ошибка (`miette`) с подсветкой.
    ///
    ///
    /// ## 2. Разбор операторов после левой части (postfix и infix)
    ///
    /// После получения начального `lhs` метод заходит в цикл и смотрит на следующий токен.
    ///
    /// Поддерживаются **постфиксные операторы**:
    /// - вызов функции: `lhs(...)`  
    /// - доступ к полю: `lhs.field`  
    ///
    /// Постфиксные операторы проверяются через `postfix_binding_power(op)`.  
    /// Если их приоритет ниже `min_bp`, разбор завершается.
    ///
    /// Поддерживаются **инфиксные операторы**:
    /// - `+`, `-`, `*`, `/`
    /// - `==`, `!=`
    /// - `<`, `<=`, `>`, `>=`
    /// - `and`, `or`
    ///
    /// Здесь применяется `infix_binding_power(op)`, который возвращает `(l_bp, r_bp)` —
    /// приоритеты для левой и правой частей.  
    /// Если `l_bp < min_bp`, текущий уровень разбора заканчивается.
    ///
    /// Иначе:
    /// 1. оператор считывается (`lexer.next()`),  
    /// 2. рекурсивно вызывается разбор правой части:  
    ///    `self.parse_expression_within(r_bp)`  
    /// 3. формируется новая вершина AST:  
    ///    `TokenTree::Cons(op, vec![lhs, rhs])`
    ///
    ///
    /// ## 3. Завершение разбора
    /// Когда:
    /// - токен отсутствует,  
    /// - или это токен, завершающий выражение (`)`, `}`, `,`, `;`),  
    /// - или сила связывания следующего оператора недостаточна,  
    ///  
    /// цикл разбора завершается, и метод возвращает построенное дерево выражения.
    ///
    ///
    /// # Параметры
    /// * `min_bp` — минимальная сила связывания оператора.  
    ///   Используется при рекурсивных вызовах для реализации приоритета операторов.
    ///
    ///
    /// # Результат
    /// Возвращает [`TokenTree`] — дерево разбора выражения.
    ///
    /// Если входные токены закончились, возвращает:  
    /// `TokenTree::Atom(Atom::Nil)`.
    ///
    ///
    /// # Обработка ошибок
    /// Ошибки формируются через библиотеку [`miette`], с подсветкой исходного кода.
    /// Каждая вложенная ошибка имеет контекст (`wrap_err`, `wrap_err_with`).
    ///
    ///
    /// # Примеры
    ///
    /// ```text
    /// Вход:   1 + 2 * 3
    /// Выход:  Cons(Plus, [1, Cons(Star, [2, 3])])
    ///
    /// Вход:   -(a + b)
    /// Выход:  Cons(Minus, [Cons(Group, [Cons(Plus, [a, b])])])
    ///
    /// Вход:   foo(1, 2).bar > 0
    /// Выход:  Cons(Greater, [
    ///             Cons(Field, [
    ///                 Call { callee: foo, arguments: [1, 2] },
    ///                 Ident("bar")
    ///             ]),
    ///             0
    ///         ])
    /// ```
    ///
    /// # Краткое описание грамматики
    ///
    /// ```text
    /// expression := prefix (postfix | infix expression)*
    ///
    /// prefix     := literal
    ///             | ident
    ///             | this | super
    ///             | ( expression )
    ///             | - prefix
    ///             | ! prefix
    ///
    /// postfix    := ( arguments ) | . ident
    /// infix      := + | - | * | / | == | != | < | <= | > | >= | and | or
    /// ```
    pub fn parse_expression_within(&mut self, min_bp: u8) -> Result<TokenTree<'de>, Error> {
        let lhs = match self.lexer.next() {
            Some(Ok(token)) => token,
            None => return Ok(TokenTree::Atom(Atom::Nil)),
            Some(Err(e)) => {
                return Err(e).wrap_err("on left-hand side");
            }
        };
        let mut lhs =
            match lhs {
                // atoms
                Token {
                    kind: TokenKind::String,
                    origin,
                    ..
                } => TokenTree::Atom(Atom::String(Token::unescape(origin))),
                Token {
                    kind: TokenKind::Number(n),
                    ..
                } => TokenTree::Atom(Atom::Number(n)),
                Token {
                    kind: TokenKind::True,
                    ..
                } => TokenTree::Atom(Atom::Bool(true)),
                Token {
                    kind: TokenKind::False,
                    ..
                } => TokenTree::Atom(Atom::Bool(false)),
                Token {
                    kind: TokenKind::Nil,
                    ..
                } => TokenTree::Atom(Atom::Nil),
                Token {
                    kind: TokenKind::Ident,
                    origin,
                    ..
                } => TokenTree::Atom(Atom::Ident(origin)),
                Token {
                    kind: TokenKind::Super,
                    ..
                } => TokenTree::Atom(Atom::Super),

                Token {
                    kind: TokenKind::This,
                    ..
                } => TokenTree::Atom(Atom::This),

                // groups
                Token {
                    kind: TokenKind::LeftParen,
                    ..
                } => {
                    let lhs = self
                        .parse_expression_within(0)
                        .wrap_err("in bracketed expression")?;
                    self.lexer
                        .expect(
                            TokenKind::RightParen,
                            "Unexpected end to bracketed expression",
                        )
                        .wrap_err("after bracketed expression")?;
                    TokenTree::Cons(Operator::Group, vec![lhs])
                }

                // unary prefix expressions
                Token {
                    kind: TokenKind::Bang | TokenKind::Minus,
                    ..
                } => {
                    let op = match lhs.kind {
                        TokenKind::Bang => Operator::Bang,
                        TokenKind::Minus => Operator::Minus,
                        _ => unreachable!("by the outer match arm pattern"),
                    };
                    let ((), r_bp) = prefix_binding_power(op);
                    let rhs = self
                        .parse_expression_within(r_bp)
                        .wrap_err("in right-hand side")?;
                    TokenTree::Cons(op, vec![rhs])
                }

                token => return Err(miette::miette! {
                    labels = vec![
                        LabeledSpan::at(token.offset..token.offset + token.origin.len(), "here"),
                    ],
                    help = format!("Unexpected {token:?}"),
                    "Expected an expression",
                }
                .with_source_code(self.whole.to_string())),
            };

        loop {
            let op = self.lexer.peek();
            if op.map_or(false, |op| op.is_err()) {
                return Err(self
                    .lexer
                    .next()
                    .expect("checked Some above")
                    .expect_err("checked Err above"))
                .wrap_err("in place of expected operator");
            }
            let op = match op.map(|res| res.as_ref().expect("handled Err above")) {
                None => break,

                Some(Token {
                    kind:
                        TokenKind::RightParen
                        | TokenKind::Comma
                        | TokenKind::Semicolon
                        | TokenKind::RightBrace,
                    ..
                }) => break,
                Some(Token {
                    kind: TokenKind::LeftParen,
                    ..
                }) => Operator::Call,
                Some(Token {
                    kind: TokenKind::Dot,
                    ..
                }) => Operator::Field,
                Some(Token {
                    kind: TokenKind::Minus,
                    ..
                }) => Operator::Minus,
                Some(Token {
                    kind: TokenKind::Plus,
                    ..
                }) => Operator::Plus,
                Some(Token {
                    kind: TokenKind::Star,
                    ..
                }) => Operator::Star,
                Some(Token {
                    kind: TokenKind::BangEqual,
                    ..
                }) => Operator::BangEqual,
                Some(Token {
                    kind: TokenKind::EqualEqual,
                    ..
                }) => Operator::EqualEqual,
                Some(Token {
                    kind: TokenKind::LessEqual,
                    ..
                }) => Operator::LessEqual,
                Some(Token {
                    kind: TokenKind::GreaterEqual,
                    ..
                }) => Operator::GreaterEqual,
                Some(Token {
                    kind: TokenKind::Less,
                    ..
                }) => Operator::Less,
                Some(Token {
                    kind: TokenKind::Greater,
                    ..
                }) => Operator::Greater,
                Some(Token {
                    kind: TokenKind::Slash,
                    ..
                }) => Operator::Slash,
                Some(Token {
                    kind: TokenKind::And,
                    ..
                }) => Operator::And,
                Some(Token {
                    kind: TokenKind::Or,
                    ..
                }) => Operator::Or,

                Some(token) => return Err(miette::miette! {
                    labels = vec![
                        LabeledSpan::at(token.offset..token.offset + token.origin.len(), "here"),
                    ],
                    help = format!("Unexpected {token:?}"),
                    "Expected an infix operator",
                }
                .with_source_code(self.whole.to_string())),
            };

            if let Some((l_bp, ())) = postfix_binding_power(op) {
                if l_bp < min_bp {
                    break;
                }
                self.lexer.next();

                lhs = match op {
                    Operator::Call => TokenTree::Call {
                        callee: Box::new(lhs),
                        arguments: self
                            .parse_fun_call_arguments()
                            .wrap_err("in function call arguments")?,
                    },
                    _ => TokenTree::Cons(op, vec![lhs]),
                };
                continue;
            }

            if let Some((l_bp, r_bp)) = infix_binding_power(op) {
                if l_bp < min_bp {
                    break;
                }
                self.lexer.next();

                lhs = match op {
                    // TODO: ternary
                    // let mhs = self.parse_within(0);
                    // assert_eq!(lexer.next(), Token::Operator(':'));
                    // let rhs = self.parse_within(r_bp);
                    // TokenTree::Cons(op, vec![lhs, mhs, rhs])
                    _ => {
                        let rhs = self
                            .parse_expression_within(r_bp)
                            .wrap_err_with(|| format!("on the right-hand side of {lhs} {op}"))?;
                        TokenTree::Cons(op, vec![lhs, rhs])
                    }
                };
                continue;
            }

            break;
        }

        Ok(lhs)
    }
}

/// Простейший атомарный элемент синтаксического дерева.
/// 
/// `Atom` соответствует "листу" в AST: строке, числу, идентификатору,
/// `true`/`false`, `nil`, а также ключевым словам `super` и `this`.
///
/// Эти значения не имеют детей и являются минимальными строительными блоками
/// выражений. Все более сложные конструкции (вызовы функций, операторы,
/// бинарные выражения) строятся вокруг них.
#[derive(Debug, Clone, PartialEq)]
pub enum Atom<'de> {
    String(Cow<'de, str>),
    Number(f64),
    Nil,
    Bool(bool),
    Ident(&'de str),
    Super,
    This,
}

impl fmt::Display for Atom<'_> {
    /// Человекочитаемое представление атома.
    /// Используется в pretty-printing AST и при выводе ошибок.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Atom::String(s) => write!(f, "\"{s}\""), // ← фикс: строки всегда в кавычках
            Atom::Number(n) => {
                if *n == n.trunc() {
                    write!(f, "{n}.0")
                } else {
                    write!(f, "{n}")
                }
            }
            Atom::Nil => write!(f, "nil"),
            Atom::Bool(b) => write!(f, "{b}"),
            Atom::Ident(i) => write!(f, "{i}"),
            Atom::Super => write!(f, "super"),
            Atom::This => write!(f, "this"),
        }
    }
}


/// Операторы языка и специальные псевдо-операторы.
/// 
/// Этот enum включает арифметические (`+`, `-`, `*`, `/`),
/// сравнения (`==`, `<`, `>=`, ...),
/// логические (`and`, `or`),
/// обращение к полю (`.`),
/// вызов функции (`call`),
/// группировку (`group`),
/// а также операторы управления (`for`, `while`, `return`, `print`, …).
///
/// Некоторые операторы имеют связность и приоритет,
/// определяемые функциями `prefix_binding_power`, `postfix_binding_power`
/// и `infix_binding_power`.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Operator {
    Minus,
    Plus,
    Star,
    BangEqual,
    EqualEqual,
    LessEqual,
    GreaterEqual,
    Less,
    Greater,
    Slash,
    Bang,
    And,
    Or,
    Call,
    For,
    Class,
    Print,
    Return,
    Field,
    Var,
    While,
    Group,
}

impl fmt::Display for Operator {
    /// Человекочитаемый вывод оператора.
    /// Используется в pretty-printing AST и сообщениях об ошибках.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = match self {
            Operator::Minus         => "-",
            Operator::Plus          => "+",
            Operator::Star          => "*",
            Operator::Slash         => "/",
            Operator::Bang          => "!",
            Operator::BangEqual     => "!=",
            Operator::EqualEqual    => "==",
            Operator::Less          => "<",
            Operator::LessEqual     => "<=",
            Operator::Greater       => ">",
            Operator::GreaterEqual  => ">=",
            Operator::And           => "and",
            Operator::Or            => "or",
            Operator::Call          => "call",
            Operator::For           => "for",
            Operator::Class         => "class",
            Operator::Print         => "print",
            Operator::Return        => "return",
            Operator::Field         => ".",
            Operator::Var           => "var",
            Operator::While         => "while",
            Operator::Group         => "group",
        };
        write!(f, "{s}")
    }
}

/// Узел абстрактного синтаксического дерева (AST).
///
/// `TokenTree` описывает всю структуру синтаксиса:
/// выражения, вызовы функций, операторы, ветвления и объявления функций.
///
/// Это основная структура, которую выдаёт парсер.
#[derive(Debug, Clone, PartialEq)]
pub enum TokenTree<'de> {
    Atom(Atom<'de>),
    Cons(Operator, Vec<TokenTree<'de>>),
    Fun {
        name: Atom<'de>,
        parameters: Vec<Token<'de>>,
        body: Box<TokenTree<'de>>,
    },
    Call {
        callee: Box<TokenTree<'de>>,
        arguments: Vec<TokenTree<'de>>,
    },
    If {
        condition: Box<TokenTree<'de>>,
        yes: Box<TokenTree<'de>>,
        no: Option<Box<TokenTree<'de>>>,
    },
}
impl fmt::Display for TokenTree<'_> {
    /// Лиспоподобный вывод AST — удобный для тестов и логгирования
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {

            TokenTree::Atom(a) => write!(f, "{a}"),

            TokenTree::Cons(head, tail) => {
                write!(f, "({}", head)?;
                for item in tail {
                    write!(f, " {item}")?;
                }
                write!(f, ")")
            }

            TokenTree::Fun { name, parameters, body } => {
                write!(f, "(fun {name} (")?;
                for (i, p) in parameters.iter().enumerate() {
                    if i > 0 { write!(f, " ")? }
                    write!(f, "{p}")?;
                }
                write!(f, ") {body})")
            }

            TokenTree::Call { callee, arguments } => {
                write!(f, "(call {callee}")?;
                for a in arguments {
                    write!(f, " {a}")?;
                }
                write!(f, ")")
            }

            TokenTree::If { condition, yes, no } => {
                write!(f, "(if {condition} {yes}")?;
                if let Some(no) = no {
                    write!(f, " {no}")?;
                }
                write!(f, ")")
            }
        }
    }
}

/// Приоритет и связность унарных операторов.
/// 
/// Возвращает:
/// - `()` — фиктивное значение слева (у унарных операторов нет "левого" аргумента)
/// - `r_bp` — правый приоритет (лексемы справа должны иметь такой же или более высокий приоритет)
fn prefix_binding_power(op: Operator) -> ((), u8) {
    match op {
        Operator::Print | Operator::Return => ((), 1),
        Operator::Bang | Operator::Minus => ((), 11),
        _ => panic!("bad op: {:?}", op),
    }
}

/// Приоритет постфиксных операторов (например, вызов функции).
///
/// Возвращает `(l_bp, ())`, где:
/// - `l_bp` — левый приоритет: выражение слева должно иметь приоритет не ниже этого.
/// - `()` — фиктивное значение справа (у постфиксных операторов нет правого выражения).
fn postfix_binding_power(op: Operator) -> Option<(u8, ())> {
    let res = match op {
        Operator::Call => (13, ()),
        _ => return None,
    };
    Some(res)
}


/// Приоритет бинарных операторов.
///
/// Возвращает `(l_bp, r_bp)`:
/// - `l_bp` — требуемый приоритет слева  
/// - `r_bp` — приоритет выражения справа
///
/// Используется алгоритмом Прэтта для реализации рекурсивного спуска с приоритетами.

fn infix_binding_power(op: Operator) -> Option<(u8, u8)> {
    let res = match op {
        Operator::And | Operator::Or => (3, 4),
        Operator::BangEqual
        | Operator::EqualEqual
        | Operator::Less
        | Operator::LessEqual
        | Operator::Greater
        | Operator::GreaterEqual => (5, 6),
        Operator::Plus | Operator::Minus => (7, 8),
        Operator::Star | Operator::Slash => (9, 10),
        Operator::Field => (16, 15),
        _ => return None,
    };
    Some(res)
}