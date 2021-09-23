use kuchiki::traits::*;
use std::{env, fs::File, io::prelude::*, path::PathBuf, str};

fn dash_to_pascal(s: &str) -> String {
    let ret = s
        .split('-')
        .filter(|s| !s.is_empty())
        .map(|s| s[..1].to_ascii_uppercase() + &s[1..])
        .collect::<Vec<_>>()
        .join("");
    if ret
        .chars()
        .next()
        .as_ref()
        .map_or(false, char::is_ascii_digit)
    {
        "Namespace".to_owned() + &ret
    } else {
        ret
    }
}

struct Namespace {
    nid: String,
    templates: Vec<String>,
    reference: Vec<String>,
}

// table-urn-namespaces-1
// table-urn-namespaces-2
fn list(html: &str, table_selector: &str) -> impl Iterator<Item = Namespace> {
    let html = kuchiki::parse_html().one(html);
    let table = html.select_first(table_selector).unwrap();
    let tbody = table.as_node().select_first("tbody").unwrap();
    tbody.as_node().select("tr").unwrap().map(
            |row| {
                let mut td = row.as_node().select("td").unwrap();
                let nid = td.next().unwrap().as_node().text_contents();
                let mut get_links = || td.next().unwrap().as_node().select("a").unwrap().map(|link| {
                    let link = link.as_node();
                    let url = link.as_element().unwrap().attributes.borrow().get("href").unwrap().to_owned();
                    let url = if url.starts_with('#') {
                        format!("https://www.iana.org/assignments/urn-namespaces/urn-namespaces.xhtml{}", url)
                    } else {
                        url
                    };
                    format!("[{}]({})", link.text_contents(), url)
                }).collect::<Vec<String>>();
                let templates = get_links();
                let reference = get_links();
                Namespace {
                    nid,
                    templates,
                    reference,
                }
            }
        )
}

fn list_formal(html: &str) -> impl Iterator<Item = Namespace> {
    list(html, "#table-urn-namespaces-1")
}

fn list_informal(html: &str) -> impl Iterator<Item = Namespace> {
    list(html, "#table-urn-namespaces-2")
}

fn main() {
    let url = "https://www.iana.org/assignments/urn-namespaces/urn-namespaces.xhtml";
    let body = reqwest::blocking::get(url)
        .ok()
        .filter(|resp| resp.status().is_success())
        .and_then(move |resp| resp.bytes().ok().map(|x| x.to_vec()))
        .unwrap_or_else(|| include_bytes!("urn-namespaces.xhtml").to_vec());
    let body = str::from_utf8(&body).unwrap();
    let out_path = PathBuf::from(env::var("OUT_DIR").unwrap());
    let mut file = File::create(out_path.join("generated.rs")).unwrap();
    writeln!(file, "#[non_exhaustive]").unwrap();
    writeln!(file, "#[derive(Debug, Eq, PartialEq, Clone, Hash)]").unwrap();
    writeln!(file, "/// A URN namespace identifier").unwrap();
    writeln!(file, "pub enum Namespace {{").unwrap();
    for record in list_formal(body) {
        let mut comment = Vec::new();
        comment.push(format!("Formal namespace: `{}`", record.nid));
        if !record.templates.is_empty() {
            comment.push(format!("Template: {}", record.templates.join("; ")));
        }
        if !record.reference.is_empty() {
            comment.push(format!("Reference: {}", record.reference.join("; ")));
        }
        for c in comment {
            writeln!(file, "    /// {}.", c).unwrap();
        }
        writeln!(file, "    /// Sourced from [the IANA namespace registry](https://www.iana.org/assignments/urn-namespaces/urn-namespaces.xhtml).").unwrap();
        writeln!(file, "    {},", dash_to_pascal(&record.nid)).unwrap();
    }
    for record in list_informal(body) {
        let mut comment = Vec::new();
        comment.push(format!("Informal namespace: `{}`", record.nid));
        if !record.templates.is_empty() {
            comment.push(format!("Template: {}", record.templates.join("; ")));
        }
        if !record.reference.is_empty() {
            comment.push(format!("Reference: {}", record.reference.join("; ")));
        }
        for c in comment {
            writeln!(file, "    /// {}.", c).unwrap();
        }
        writeln!(file, "    /// Sourced from [the IANA namespace registry](https://www.iana.org/assignments/urn-namespaces/urn-namespaces.xhtml).").unwrap();
        writeln!(file, "    {},", dash_to_pascal(&record.nid)).unwrap();
    }
    writeln!(file, "    Unknown(").unwrap();
    writeln!(file, "        /// The unknown NID. Must follow the [NID syntax rules](https://datatracker.ietf.org/doc/html/rfc8141#section-2)!").unwrap();
    writeln!(file, "        String,").unwrap();
    writeln!(file, "    ),").unwrap();
    writeln!(file, "}}").unwrap();
    writeln!(file).unwrap();
    writeln!(file, "impl Namespace {{").unwrap();
    writeln!(
        file,
        "    /// Check whether the namespace is formal (as defined by IANA)"
    )
    .unwrap();
    writeln!(file, "    pub fn is_formal(&self) -> bool {{").unwrap();
    writeln!(file, "        matches!(self,").unwrap();
    writeln!(
        file,
        "{}",
        list_formal(body)
            .map(|x| format!("Self::{}", dash_to_pascal(&x.nid)))
            .collect::<Vec<_>>()
            .join(" |\n            ")
    )
    .unwrap();
    writeln!(file, "        )").unwrap();
    writeln!(file, "    }}").unwrap();
    writeln!(file).unwrap();
    writeln!(
        file,
        "    /// Check whether the namespace is informal (as defined by IANA)"
    )
    .unwrap();
    writeln!(file, "    pub fn is_informal(&self) -> bool {{").unwrap();
    writeln!(file, "        matches!(self,").unwrap();
    writeln!(
        file,
        "{}",
        list_informal(body)
            .map(|x| format!("Self::{}", dash_to_pascal(&x.nid)))
            .collect::<Vec<_>>()
            .join(" |\n            ")
    )
    .unwrap();
    writeln!(file, "        )").unwrap();
    writeln!(file, "    }}").unwrap();
    writeln!(file).unwrap();
    writeln!(file, "    pub fn new(id: &str) -> Result<Self> {{").unwrap();
    writeln!(file, "        match id.to_ascii_lowercase().as_str() {{").unwrap();
    for record in list_formal(body) {
        writeln!(
            file,
            "            \"{}\" => Ok(Self::{}),",
            record.nid,
            dash_to_pascal(&record.nid),
        )
        .unwrap();
    }
    for record in list_informal(body) {
        writeln!(
            file,
            "            \"{}\" => Ok(Self::{}),",
            record.nid,
            dash_to_pascal(&record.nid),
        )
        .unwrap();
    }
    writeln!(
        file,
        "            s if is_valid_nid(s) => Ok(Self::Unknown(s.to_owned())),"
    )
    .unwrap();
    writeln!(file, "            _ => Err(Error::InvalidNid),").unwrap();
    writeln!(file, "        }}").unwrap();
    writeln!(file, "    }}").unwrap();
    writeln!(file, "}}").unwrap();
    writeln!(file).unwrap();
    writeln!(file, "impl fmt::Display for Namespace {{").unwrap();
    writeln!(
        file,
        "    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> result::Result<(), fmt::Error> {{"
    )
    .unwrap();
    writeln!(file, "        write!(f, \"{{}}\", match self {{").unwrap();
    for record in list_formal(body) {
        writeln!(
            file,
            "            Self::{} => \"{}\",",
            dash_to_pascal(&record.nid),
            record.nid,
        )
        .unwrap();
    }
    for record in list_informal(body) {
        writeln!(
            file,
            "            Self::{} => \"{}\",",
            dash_to_pascal(&record.nid),
            record.nid,
        )
        .unwrap();
    }
    writeln!(file, "            Self::Unknown(s) => s,").unwrap();
    writeln!(file, "        }})").unwrap();
    writeln!(file, "    }}").unwrap();
    writeln!(file, "}}").unwrap();
}
