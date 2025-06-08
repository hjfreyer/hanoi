use std::collections::VecDeque;

use itertools::{Itertools, Position};
use ratatui::{
    crossterm::event,
    layout::{Constraint, Layout},
    style::{Style, Stylize},
    text::Text,
    widgets::{Paragraph, Row, Table, TableState},
    DefaultTerminal,
};

use crate::{
    flat::ValueView,
    source::{self},
    vm::{EvalError, StepResult, Vm, VmState},
};

pub struct Debugger {
    sources: source::Sources,
    vm: Vm,
    history: VecDeque<VmState>,

    highlight_span: Option<source::FileSpan>,
    code_scroll: u16,
    stack_state: TableState,
    error: Option<EvalError>,
    halted: bool,
}

const HISTORY_WINDOW: usize = 500;

impl Debugger {
    fn step(&mut self) {
        if self.error.is_some() || self.halted {
            return;
        }

        match self.vm.step() {
            Ok(None) => {
                if HISTORY_WINDOW < self.history.len() {
                    self.history.pop_front();
                }
                self.history.push_back(self.vm.save_state());
                self.update_code();
            }
            Ok(Some(_)) => self.halted = true,
            Err(err) => {
                self.error = Some(err);
            }
        }
    }

    fn update_code(&mut self) {
        if let Some(word) = self.vm.current_word() {
            self.highlight_span = Some(word.span);
            let (line, _) = word.span.as_pest(&self.sources).start_pos().line_col();
            self.code_scroll = (line as u16).saturating_sub(10);
        }
    }

    pub fn step_back(&mut self) {
        self.vm.restore_state(self.history.pop_back().unwrap());
        self.error = None;
        self.halted = false;
        self.update_code();
    }

    fn next_line(&mut self) {
        while self.error.is_none() && !self.halted && self.highlight_span.is_none() {
            self.step()
        }
        if self.error.is_some() || self.halted {
            return;
        }

        let current_line = self
            .highlight_span
            .expect("ran until current word was some")
            .location(&self.sources)
            .line;

        while self.error.is_none()
            && !self.halted
            && self
                .highlight_span
                .map(|span| span.as_pest(&self.sources).start_pos().line_col().0 == current_line)
                .unwrap_or(true)
        {
            self.step()
        }
    }

    // fn jump_over(&mut self) {
    //     let current_line = self
    //         .highlight_span
    //         .expect("ran until current word was some")
    //         .start_pos()
    //         .line_col()
    //         .0;
    //     self.finish_sentence();
    //     if self.error.is_some() {
    //         return;
    //     }

    //     let return_address = self.vm.stack.get(1).expect("no return address?");
    //     let &Value::Pointer(Closure(_, sidx)) = return_address else {
    //         panic!("return address not a closure?")
    //     };

    //     while self.error.is_none() && self.vm.call_stack.sentence_idx != sidx {
    //         self.step()
    //     }
    //     while self.error.is_none()
    //         && self
    //             .highlight_span
    //             .map(|span| span.start_pos().line_col().0 == current_line)
    //             .unwrap_or(true)
    //     {
    //         self.step()
    //     }
    // }

    // fn finish_sentence(&mut self) {
    //     while self.error.is_none()
    //         && self.vm.call_stack.word_idx != self.vm.lib.sentences[self.vm.call_stack.sentence_idx].words.len() - 1
    //     {
    //         self.step();
    //     }
    // }

    fn code(&self) -> Paragraph {
        let text = if let Some(span) = self.highlight_span {
            let span = span.as_pest(&self.sources);
            let code = span.get_input();
            let mut res = Text::raw("");
            for line in code[..span.start()].lines() {
                res.push_line(line);
            }
            for (pos, line) in span.as_str().lines().with_position() {
                if pos == Position::First || pos == Position::Only {
                    res.push_span(line.on_green());
                } else {
                    res.push_line(line.on_green());
                }
            }
            for (pos, line) in code[span.end()..].lines().with_position() {
                if pos == Position::First || pos == Position::Only {
                    res.push_span(line);
                } else {
                    res.push_line(line);
                }
            }
            res
        } else {
            Text::raw("???")
        };
        Paragraph::new(text)
            .scroll((self.code_scroll, 0))
            .white()
            .on_blue()
    }

    fn stack(&self) -> Table<'static> {
        let names = self
            .vm
            .current_word()
            .and_then(|w| w.names.clone())
            .unwrap_or_else(|| self.vm.stack.iter().map(|_| None).collect());

        let names_width = names
            .iter()
            .filter_map(|n| n.as_ref().map(|s| s.len()))
            .max()
            .unwrap_or_default();

        let mut items: Vec<Row> = self
            .vm
            .stack
            .iter()
            .rev()
            .zip_longest(names.iter())
            .map(|v| {
                let (v, name) = v.left_and_right();
                let v = v
                    .map(|v| {
                        ValueView {
                            sources: &self.sources,
                            value: v,
                        }
                        .to_string()
                    })
                    .unwrap_or_else(|| "???".to_owned());
                let name = name.and_then(|n| n.clone()).unwrap_or_default();
                Row::new([name, " = ".to_owned(), v])
            })
            .collect();
        items.reverse();
        Table::new(
            items,
            [
                Constraint::Length(names_width as u16),
                Constraint::Length(3),
                Constraint::Fill(1),
            ],
        )
        .column_spacing(0)
        .highlight_style(Style::new().black().on_white())
    }

    fn word_text(&self) -> Text {
        let Some(word) = self.vm.current_word() else {
            return Text::default();
        };
        Text::raw(format!("{:?}", word.inner)).red().on_dark_gray()
    }

    fn error_text(&self) -> Text {
        let Some(err) = &self.error else {
            return Text::default();
        };
        Text::raw(err.to_string()).red().on_dark_gray()
    }

    fn render_program(&mut self, frame: &mut ratatui::Frame) {
        let layout = Layout::horizontal(Constraint::from_percentages([50, 50])).split(frame.area());

        let word_text = self.word_text();
        let err_text = self.error_text();
        let stack_layout = Layout::vertical([
            Constraint::Percentage(100),
            Constraint::Min(word_text.height() as u16),
            Constraint::Min(err_text.height() as u16),
        ])
        .split(layout[1]);

        frame.render_widget(self.code(), layout[0]);
        frame.render_widget(word_text, stack_layout[1]);
        frame.render_widget(err_text, stack_layout[2]);
        frame.render_stateful_widget(self.stack(), stack_layout[0], &mut self.stack_state);
    }

    pub fn new(sources: source::Sources, vm: crate::vm::Vm) -> Self {
        let mut res = Self {
            sources,
            vm,
            history: VecDeque::new(),
            stack_state: TableState::default(),
            error: None,
            halted: false,

            code_scroll: 0,
            highlight_span: None,
        };
        res.update_code();
        res
    }
}

pub fn run(mut terminal: DefaultTerminal, mut debugger: Debugger) -> std::io::Result<()> {
    loop {
        terminal.draw(|frame| {
            debugger.render_program(frame);
            // frame.render_widget(greeting, frame.area());
        })?;

        if let event::Event::Key(key) = event::read()? {
            if key.kind == event::KeyEventKind::Press && key.code == event::KeyCode::Char('q') {
                return Ok(());
            }

            if key.kind == event::KeyEventKind::Press && key.code == event::KeyCode::Char('s') {
                debugger.next_line();
            }

            if key.kind == event::KeyEventKind::Press && key.code == event::KeyCode::Char('n') {
                // debugger.jump_over();
                todo!()
            }

            if key.kind == event::KeyEventKind::Press && key.code == event::KeyCode::Left {
                debugger.step_back();
            }
            if key.kind == event::KeyEventKind::Press && key.code == event::KeyCode::Right {
                debugger.step();
            }
            if key.kind == event::KeyEventKind::Press && key.code == event::KeyCode::Up {
                debugger.code_scroll = debugger.code_scroll.saturating_sub(1);
                // debugger.stack_state.select_previous();
            }
            if key.kind == event::KeyEventKind::Press && key.code == event::KeyCode::Down {
                debugger.code_scroll = debugger.code_scroll.saturating_add(1);
                // debugger.stack_state.select_next();
            }
        }
    }
}
