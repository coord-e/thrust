//! Attachable debug information for CHC clauses.
//!
//! The [`DebugInfo`] struct captures contextual information (like `tracing` spans) at the time
//! of a clause's creation. This information is then pretty-printed as comments in the
//! generated SMT-LIB2 file, which helps in tracing a clause back to its origin in the
//! Thrust codebase and in the analyzed program.
//!
//! The span fields it reads are recorded by [`DebugInfoLayer`], which has to be registered on the
//! `tracing` subscriber without a level filter: the origin of a clause is wanted whether or not
//! the user asked for any logging.

use tracing_subscriber::registry::LookupSpan;

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

/// The fields of a single `tracing` span, kept in the span's extensions by [`DebugInfoLayer`].
#[derive(Debug, Default)]
struct SpanFields {
    fields: Vec<(String, String)>,
}

impl tracing::field::Visit for SpanFields {
    fn record_str(&mut self, field: &tracing::field::Field, value: &str) {
        self.fields
            .push((field.name().to_owned(), value.to_owned()));
    }

    fn record_debug(&mut self, field: &tracing::field::Field, value: &dyn std::fmt::Debug) {
        self.fields
            .push((field.name().to_owned(), format!("{:?}", value)));
    }
}

/// A `tracing` layer that records span fields for [`DebugInfo::from_current_span`].
pub struct DebugInfoLayer;

impl<S> tracing_subscriber::Layer<S> for DebugInfoLayer
where
    S: tracing::Subscriber + for<'a> LookupSpan<'a>,
{
    fn on_new_span(
        &self,
        attrs: &tracing::span::Attributes<'_>,
        id: &tracing::span::Id,
        ctx: tracing_subscriber::layer::Context<'_, S>,
    ) {
        let mut span_fields = SpanFields::default();
        attrs.record(&mut span_fields);
        let span = ctx.span(id).expect("span of a just-created id");
        span.extensions_mut().insert(span_fields);
    }

    fn on_record(
        &self,
        id: &tracing::span::Id,
        values: &tracing::span::Record<'_>,
        ctx: tracing_subscriber::layer::Context<'_, S>,
    ) {
        let span = ctx.span(id).expect("span of a recorded id");
        let mut extensions = span.extensions_mut();
        let span_fields = extensions
            .get_mut::<SpanFields>()
            .expect("span fields inserted on creation");
        values.record(span_fields);
    }
}

impl DebugInfo {
    pub fn from_current_span() -> Self {
        let mut debug_info = Self::default();
        debug_info.context_from_current_span();
        debug_info
    }

    /// Records the name and the fields of the enclosing `tracing` spans.
    ///
    /// The spans are visited innermost first, and a field that several of them carry -- the source
    /// location, for one -- is taken from the innermost, which describes the clause most closely.
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
            use tracing_subscriber::registry::SpanData;
            let mut span_id = current_span.id().cloned();
            while let Some(id) = span_id {
                let Some(data) = registry.span_data(&id) else {
                    break;
                };
                let extensions = data.extensions();
                if let Some(span_fields) = extensions.get::<SpanFields>() {
                    for (key, value) in &span_fields.fields {
                        if !self.has_context(key) {
                            self.context(key, value.clone());
                        }
                    }
                }
                span_id = data.parent().cloned();
            }
        });
    }

    fn has_context(&self, key: &str) -> bool {
        self.contexts.iter().any(|(k, _)| k == key)
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

    pub fn display(&self, line_head: &'static str) -> Display<'_> {
        Display {
            inner: self,
            line_head,
        }
    }
}
