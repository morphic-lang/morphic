use std::io::Write;

#[derive(Debug, thiserror::Error)]
pub enum Error {
    #[error(transparent)]
    Io(#[from] std::io::Error),
    #[error("digraphs cannot be nested")]
    NestedDigraph,
    #[error("unsupported graphviz output format: {0}")]
    UnsupportedFormat(String),
}

#[derive(Debug, Clone)]
pub struct GraphvizWriter {
    tabwidth: u32,
    depth: u32,
    node_count: u32,
    cluster_count: u32,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct NodeId(u32);

impl GraphvizWriter {
    pub fn new(tabwidth: u32) -> Self {
        Self {
            tabwidth,
            depth: 0,
            node_count: 0,
            cluster_count: 0,
        }
    }

    fn write_indent<W: Write>(&self, w: &mut W) -> Result<(), Error> {
        for _ in 0..self.depth * self.tabwidth {
            write!(w, " ")?;
        }
        Ok(())
    }

    pub fn write_digraph<W, F>(&mut self, w: &mut W, f: F) -> Result<(), Error>
    where
        W: Write,
        F: FnOnce(&mut W, &mut GraphvizWriter) -> Result<(), Error>,
    {
        if self.depth > 0 {
            return Err(Error::NestedDigraph);
        }

        writeln!(w, "digraph {{")?;
        self.depth += 1;

        f(w, self)?;

        self.depth -= 1;
        writeln!(w, "}}")?;
        Ok(())
    }

    pub fn write_cluster<W, F>(&mut self, w: &mut W, label: &str, f: F) -> Result<(), Error>
    where
        W: Write,
        F: FnOnce(&mut W, &mut GraphvizWriter) -> Result<(), Error>,
    {
        self.write_indent(w)?;
        writeln!(w, "subgraph cluster_{} {{", self.cluster_count)?;
        self.depth += 1;

        self.cluster_count += 1;
        self.write_indent(w)?;
        writeln!(w, "label=\"{}\";", escape_label(label))?;
        f(w, self)?;

        self.depth -= 1;
        self.write_indent(w)?;
        writeln!(w, "}}")?;

        Ok(())
    }

    pub fn write_node<W>(
        &mut self,
        w: &mut W,
        label: &str,
        attrs: Option<&str>,
    ) -> Result<NodeId, Error>
    where
        W: Write,
    {
        let id = self.node_count;
        self.node_count += 1;

        self.write_indent(w)?;

        write!(w, "n{id} [label=\"{}\"", escape_label(label))?;
        if let Some(attrs) = attrs {
            write!(w, ", {}", attrs)?;
        }
        write!(w, "];\n")?;
        Ok(NodeId(id))
    }

    pub fn write_edge<W>(
        &mut self,
        w: &mut W,
        from: NodeId,
        to: NodeId,
        attrs: Option<&str>,
    ) -> Result<(), Error>
    where
        W: Write,
    {
        self.write_indent(w)?;
        write!(w, "n{} -> n{}", from.0, to.0)?;

        if let Some(attrs) = attrs {
            write!(w, " [{}]", attrs)?;
        }

        write!(w, ";\n")?;
        Ok(())
    }
}

fn escape_label(s: &str) -> String {
    let mut escaped = String::new();
    for c in s.chars() {
        match c {
            '"' => escaped.push_str("\\\""),
            '\\' => escaped.push_str("\\\\"),
            _ => escaped.push(c),
        }
    }
    escaped
}
