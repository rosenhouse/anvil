// The kinds a sync controller is given at boot (doc/widget_sync_fanout_design.md,
// sections 1.1 and 2.1). A kind is named `<group>/<version>/<Kind>:<selector>`
// where the selector says which field of an object names its cluster:
//
//   anvil.dev/v1/Widget:field:spec.clusterName
//   anvil.dev/v1/Gadget:name
//
// The `field:` prefix may be dropped (`anvil.dev/v1/Widget:spec.clusterName`);
// a field path must start with `spec.` and name at least one segment below it.
// Parsing is pure; discovery and the CRD shape check (crd_shape.rs) happen later.
use kube::core::GroupVersionKind;
use std::fmt;
use std::str::FromStr;

/// Which field of an object names the cluster it belongs to.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ClusterSelector {
    /// `metadata.name` is the cluster name.
    Name,
    /// A string field of the spec. The segments are the path below `spec`, so
    /// `spec.clusterName` is `Field(vec!["clusterName"])`.
    Field(Vec<String>),
}

impl ClusterSelector {
    /// The path below `spec` for a `Field` selector, `None` for `Name`.
    pub fn field_path(&self) -> Option<&[String]> {
        match self {
            ClusterSelector::Name => None,
            ClusterSelector::Field(path) => Some(path),
        }
    }

    /// The full dotted path, `spec.a.b`, for a `Field` selector, `metadata.name` for `Name`.
    pub fn dotted_path(&self) -> String {
        match self {
            ClusterSelector::Name => "metadata.name".to_string(),
            ClusterSelector::Field(path) => format!("spec.{}", path.join(".")),
        }
    }
}

impl FromStr for ClusterSelector {
    type Err = KindConfigError;

    fn from_str(s: &str) -> Result<Self, KindConfigError> {
        if s == "name" {
            return Ok(ClusterSelector::Name);
        }
        let path = s.strip_prefix("field:").unwrap_or(s);
        let below_spec = match path.strip_prefix("spec.") {
            Some(rest) => rest,
            None => {
                return Err(KindConfigError(format!(
                    "selector {:?} must be `name` or a field path starting with `spec.`",
                    s
                )))
            }
        };
        let segments: Vec<String> = below_spec.split('.').map(str::to_string).collect();
        if segments.iter().any(|seg| seg.is_empty() || !is_field_segment(seg)) {
            return Err(KindConfigError(format!(
                "field path {:?} must be dot-separated field names without empty segments",
                path
            )));
        }
        Ok(ClusterSelector::Field(segments))
    }
}

impl fmt::Display for ClusterSelector {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ClusterSelector::Name => write!(f, "name"),
            ClusterSelector::Field(_) => write!(f, "field:{}", self.dotted_path()),
        }
    }
}

// A field name as the OpenAPI schema of a CRD spells it: letters, digits, `_` and
// `-`. Anything else would not survive as a CEL identifier in the immutability rule.
fn is_field_segment(seg: &str) -> bool {
    seg.chars().all(|c| c.is_ascii_alphanumeric() || c == '_' || c == '-')
}

/// One `--kind` flag, parsed.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct KindConfig {
    pub group: String,
    pub version: String,
    pub kind: String,
    pub selector: ClusterSelector,
}

impl KindConfig {
    pub fn gvk(&self) -> GroupVersionKind {
        GroupVersionKind::gvk(&self.group, &self.version, &self.kind)
    }

    /// Parse every flag value, stopping at the first bad one.
    pub fn parse_all<I, S>(flags: I) -> Result<Vec<KindConfig>, KindConfigError>
    where
        I: IntoIterator<Item = S>,
        S: AsRef<str>,
    {
        flags.into_iter().map(|s| s.as_ref().parse()).collect()
    }
}

impl FromStr for KindConfig {
    type Err = KindConfigError;

    fn from_str(s: &str) -> Result<Self, KindConfigError> {
        let (gvk, selector) = match s.split_once(':') {
            Some(parts) => parts,
            None => {
                return Err(KindConfigError(format!(
                    "kind {:?} must be <group>/<version>/<Kind>:<selector>",
                    s
                )))
            }
        };
        let segments: Vec<&str> = gvk.split('/').collect();
        let (group, version, kind) = match segments.as_slice() {
            [group, version, kind] => (*group, *version, *kind),
            _ => {
                return Err(KindConfigError(format!(
                    "kind {:?} must name <group>/<version>/<Kind> before the colon",
                    s
                )))
            }
        };
        if group.is_empty() || version.is_empty() || kind.is_empty() {
            return Err(KindConfigError(format!(
                "kind {:?} has an empty group, version or kind",
                s
            )));
        }
        if !group.chars().all(|c| c.is_ascii_alphanumeric() || c == '.' || c == '-') {
            return Err(KindConfigError(format!("kind {:?} has a malformed group", s)));
        }
        if !version.chars().all(|c| c.is_ascii_alphanumeric()) {
            return Err(KindConfigError(format!("kind {:?} has a malformed version", s)));
        }
        if !kind.chars().all(|c| c.is_ascii_alphanumeric())
            || !kind.chars().next().is_some_and(|c| c.is_ascii_uppercase())
        {
            return Err(KindConfigError(format!(
                "kind {:?} must be a CamelCase kind name",
                s
            )));
        }
        Ok(KindConfig {
            group: group.to_string(),
            version: version.to_string(),
            kind: kind.to_string(),
            selector: selector.parse()?,
        })
    }
}

impl fmt::Display for KindConfig {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}/{}/{}:{}", self.group, self.version, self.kind, self.selector)
    }
}

/// A usage error: the flag value is not a kind.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct KindConfigError(pub String);

impl fmt::Display for KindConfigError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.0)
    }
}

impl std::error::Error for KindConfigError {}

#[cfg(test)]
mod tests {
    use super::*;

    fn field(segments: &[&str]) -> ClusterSelector {
        ClusterSelector::Field(segments.iter().map(|s| s.to_string()).collect())
    }

    #[test]
    fn parses_the_design_examples() {
        let widget: KindConfig = "anvil.dev/v1/Widget:field:spec.clusterName".parse().unwrap();
        assert_eq!(
            widget,
            KindConfig {
                group: "anvil.dev".to_string(),
                version: "v1".to_string(),
                kind: "Widget".to_string(),
                selector: field(&["clusterName"]),
            }
        );
        let gadget: KindConfig = "anvil.dev/v1/Gadget:name".parse().unwrap();
        assert_eq!(gadget.kind, "Gadget");
        assert_eq!(gadget.selector, ClusterSelector::Name);
        assert_eq!(gadget.gvk(), GroupVersionKind::gvk("anvil.dev", "v1", "Gadget"));
    }

    #[test]
    fn accepts_a_bare_field_path_and_nested_segments() {
        let k: KindConfig = "anvil.dev/v1/Widget:spec.placement.clusterName".parse().unwrap();
        assert_eq!(k.selector, field(&["placement", "clusterName"]));
        assert_eq!(k.selector.dotted_path(), "spec.placement.clusterName");
        assert_eq!(k.selector.field_path(), Some(&["placement".to_string(), "clusterName".to_string()][..]));
        assert_eq!(ClusterSelector::Name.field_path(), None);
        assert_eq!(ClusterSelector::Name.dotted_path(), "metadata.name");
    }

    #[test]
    fn display_round_trips_in_the_design_form() {
        for s in ["anvil.dev/v1/Widget:field:spec.clusterName", "anvil.dev/v1/Gadget:name"] {
            let k: KindConfig = s.parse().unwrap();
            assert_eq!(k.to_string(), s);
            assert_eq!(k.to_string().parse::<KindConfig>().unwrap(), k);
        }
        let bare: KindConfig = "anvil.dev/v1/Widget:spec.clusterName".parse().unwrap();
        assert_eq!(bare.to_string(), "anvil.dev/v1/Widget:field:spec.clusterName");
    }

    #[test]
    fn rejects_malformed_kinds() {
        let bad = [
            "",
            "anvil.dev/v1/Widget",              // no selector
            "anvil.dev/v1/Widget:",             // empty selector
            "anvil.dev/Widget:name",            // two segments
            "anvil.dev/v1/Widget/extra:name",   // four segments
            "/v1/Widget:name",                  // empty group
            "anvil.dev//Widget:name",           // empty version
            "anvil.dev/v1/:name",               // empty kind
            "anvil.dev/v1/widget:name",         // not CamelCase
            "anvil dev/v1/Widget:name",         // whitespace in group
            "anvil.dev/v1/Widget:metadata.name", // not a spec path
            "anvil.dev/v1/Widget:spec",          // no segment below spec
            "anvil.dev/v1/Widget:spec.",         // empty segment
            "anvil.dev/v1/Widget:spec..x",       // empty middle segment
            "anvil.dev/v1/Widget:spec.x.",       // trailing dot
            "anvil.dev/v1/Widget:field:",        // empty field path
            "anvil.dev/v1/Widget:field:name",    // field path must start with spec.
            "anvil.dev/v1/Widget:spec.a b",      // whitespace in a segment
            "anvil.dev/v1/Widget:Name",          // selector is case-sensitive
        ];
        for s in bad {
            assert!(s.parse::<KindConfig>().is_err(), "{:?} should not parse", s);
        }
    }

    #[test]
    fn parse_all_stops_at_the_first_bad_flag() {
        let ok = KindConfig::parse_all(["anvil.dev/v1/Widget:name", "anvil.dev/v1/Gadget:name"]).unwrap();
        assert_eq!(ok.len(), 2);
        let err = KindConfig::parse_all(["anvil.dev/v1/Widget:name", "nope"]).unwrap_err();
        assert!(err.to_string().contains("nope"), "{}", err);
        assert!(KindConfig::parse_all(Vec::<String>::new()).unwrap().is_empty());
    }
}
