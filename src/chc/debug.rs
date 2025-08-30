//! Attachable debug information for CHC clauses.
//!
//! The [`DebugInfo`] struct captures contextual information (like `tracing` spans) at the time
//! of a clause's creation. This information is then pretty-printed as comments in the
//! generated SMT-LIB2 file, which helps in tracing a clause back to its origin in the
//! Thrust codebase.

#[derive(Debug, Clone)]
pub struct Display<'a> {
    inner: &'a DebugInfo,
    line_head: &'static str,
}

impl<'a> std::fmt::Display for Display<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{}", self.line_head)?;
        for (key, value) in &self.inner.contexts {
            let mut lines = value.lines();
            write!(f, "{}={}", key, lines.next().unwrap_or_default())?;
            for line in lines {
                write!(f, "\n{}{}", self.line_head, line)?;
            }
            write!(f, " ")?;
        }
        Ok(())
    }
}

/// A purely informational metadata that can be attached to a clause.
#[derive(Debug, Clone, Default)]
pub struct DebugInfo {
    contexts: Vec<(String, String)>,
}

fn strip_ansi_colors(s: &str) -> String {
    let mut line = s.to_owned();
    let mut start = None;
    let mut offset = 0;
    for (i, b) in s.bytes().enumerate() {
        if b == b'\x1b' {
            start = Some(i);
        }
        if let Some(start_idx) = start {
            if b == b'm' {
                line.drain((start_idx - offset)..=(i - offset));
                offset += i - start_idx + 1;
                start = None;
            }
        }
    }
    line
}

impl DebugInfo {
    pub fn from_current_span() -> Self {
        let mut debug_info = Self::default();
        debug_info.context_from_current_span();
        debug_info
    }

    pub fn context_from_current_span(&mut self) {
        // XXX: hack
        tracing::dispatcher::get_default(|d| {
            let current_span = d.current_span();
            if let Some(metadata) = current_span.metadata() {
                self.context("span", metadata.name());
            }
            let Some(registry) = d.downcast_ref::<tracing_subscriber::Registry>() else {
                return;
            };
            use tracing_subscriber::registry::{LookupSpan, SpanData};
            type Extension = tracing_subscriber::fmt::FormattedFields<
                tracing_subscriber::fmt::format::DefaultFields,
            >;
            let mut span_id = current_span.id().cloned();
            while let Some(id) = span_id {
                let Some(data) = registry.span_data(&id) else {
                    break;
                };
                let exts = data.extensions();
                if let Some(fields) = exts.get::<Extension>() {
                    self.context_from_formatted_fields(&fields.fields);
                }
                span_id = data.parent().cloned();
            }
        });
    }

    fn context_from_formatted_fields(&mut self, fields: &str) {
        let mut value = None;
        for field in fields.rsplit("\x1b[2m=\x1b[0m") {
            let field = strip_ansi_colors(field);
            if let Some(prev_value) = value {
                if let Some((next_value, key)) = field.rsplit_once(' ') {
                    self.context(key, prev_value);
                    value = Some(next_value.to_owned());
                } else {
                    self.context(&field, prev_value);
                    break;
                }
            } else {
                value = Some(field);
                continue;
            }
        }
    }

    pub fn is_empty(&self) -> bool {
        self.contexts.is_empty()
    }

    pub fn context(&mut self, key: &str, value: impl Into<String>) -> &mut Self {
        self.contexts.push((key.to_owned(), value.into()));
        self
    }

    pub fn with_context(mut self, key: &str, value: impl Into<String>) -> Self {
        self.contexts.push((key.to_owned(), value.into()));
        self
    }

    pub fn display(&self, line_head: &'static str) -> Display {
        Display {
            inner: self,
            line_head,
        }
    }
}
