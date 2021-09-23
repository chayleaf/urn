use std::{env, fs::File, io::prelude::*, path::PathBuf};

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

fn main() {
    let url1 = "https://www.iana.org/assignments/urn-namespaces/urn-namespaces-1.csv";
    let url2 = "https://www.iana.org/assignments/urn-namespaces/urn-namespaces-2.csv";
    let body1 = reqwest::blocking::get(url1)
        .ok()
        .filter(|resp| resp.status().is_success())
        .and_then(move |resp| resp.bytes().ok().map(|x| x.to_vec()))
        .unwrap_or_else(|| include_bytes!("urn-namespaces-1.csv").to_vec());
    let body2 = reqwest::blocking::get(url2)
        .ok()
        .filter(|resp| resp.status().is_success())
        .and_then(move |resp| resp.bytes().ok().map(|x| x.to_vec()))
        .unwrap_or_else(|| include_bytes!("urn-namespaces-2.csv").to_vec());
    let out_path = PathBuf::from(env::var("OUT_DIR").unwrap());
    let mut file = File::create(out_path.join("generated.rs")).unwrap();
    writeln!(file, "#[non_exhaustive]").unwrap();
    writeln!(file, "#[derive(Debug, Eq, PartialEq, Clone, Hash)]").unwrap();
    writeln!(file, "/// A URN namespace identifier").unwrap();
    writeln!(file, "pub enum Namespace {{").unwrap();
    let mut rdr = csv::Reader::from_reader(body1.as_slice());
    for result in rdr.records() {
        let record = result.unwrap();
        let mut comment = Vec::new();
        comment.push(format!("Formal namespace: {}", record.get(0).unwrap()));
        match record.get(1) {
            Some(template) if !template.is_empty() => {
                comment.push(format!("Template: {}", template));
            }
            _ => {}
        }
        match record.get(2) {
            Some(reference) if !reference.is_empty() => {
                comment.push(format!("Reference: {}", reference));
            }
            _ => {}
        }
        writeln!(file, "    /// {}.", comment.join("; ")).unwrap();
        writeln!(file, "    /// See https://www.iana.org/assignments/urn-namespaces/urn-namespaces.xhtml for more info.").unwrap();
        writeln!(file, "    {},", dash_to_pascal(record.get(0).unwrap())).unwrap();
    }
    let mut rdr = csv::Reader::from_reader(body2.as_slice());
    for result in rdr.records() {
        let record = result.unwrap();
        let mut comment = Vec::new();
        comment.push(format!("Informal namespace: {}", record.get(0).unwrap()));
        match record.get(1) {
            Some(template) if !template.is_empty() => {
                comment.push(format!("Template: {}", template));
            }
            _ => {}
        }
        match record.get(2) {
            Some(reference) if !reference.is_empty() => {
                comment.push(format!("Reference: {}", reference));
            }
            _ => {}
        }
        writeln!(file, "    /// {}.", comment.join("; ")).unwrap();
        writeln!(file, "    /// See https://www.iana.org/assignments/urn-namespaces/urn-namespaces.xhtml for more info.").unwrap();
        writeln!(file, "    {},", dash_to_pascal(record.get(0).unwrap())).unwrap();
    }
    writeln!(file, "    Unknown(String),").unwrap();
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
    let mut rdr = csv::Reader::from_reader(body1.as_slice());
    writeln!(
        file,
        "{}",
        rdr.records()
            .filter_map(Result::ok)
            .map(|x| format!("Self::{}", dash_to_pascal(x.get(0).unwrap())))
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
    let mut rdr = csv::Reader::from_reader(body2.as_slice());
    writeln!(
        file,
        "{}",
        rdr.records()
            .filter_map(Result::ok)
            .map(|x| format!("Self::{}", dash_to_pascal(x.get(0).unwrap())))
            .collect::<Vec<_>>()
            .join(" |\n            ")
    )
    .unwrap();
    writeln!(file, "        )").unwrap();
    writeln!(file, "    }}").unwrap();
    writeln!(file).unwrap();
    writeln!(file, "    pub fn new(id: &str) -> Result<Self> {{").unwrap();
    writeln!(file, "        match id.to_ascii_lowercase().as_str() {{").unwrap();
    let mut rdr = csv::Reader::from_reader(body1.as_slice());
    for result in rdr.records() {
        let record = result.unwrap();
        let nid = record.get(0).unwrap();
        writeln!(
            file,
            "            \"{}\" => Ok(Self::{}),",
            nid,
            dash_to_pascal(nid),
        )
        .unwrap();
    }
    let mut rdr = csv::Reader::from_reader(body2.as_slice());
    for result in rdr.records() {
        let record = result.unwrap();
        let nid = record.get(0).unwrap();
        writeln!(
            file,
            "            \"{}\" => Ok(Self::{}),",
            nid,
            dash_to_pascal(nid),
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
    writeln!(file, "    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> result::Result<(), fmt::Error> {{").unwrap();
    writeln!(file, "        write!(f, \"{{}}\", match self {{").unwrap();
    let mut rdr = csv::Reader::from_reader(body1.as_slice());
    for result in rdr.records() {
        let record = result.unwrap();
        let nid = record.get(0).unwrap();
        writeln!(
            file,
            "            Self::{} => \"{}\",",
            dash_to_pascal(nid),
            nid,
        )
        .unwrap();
    }
    let mut rdr = csv::Reader::from_reader(body2.as_slice());
    for result in rdr.records() {
        let record = result.unwrap();
        let nid = record.get(0).unwrap();
        writeln!(
            file,
            "            Self::{} => \"{}\",",
            dash_to_pascal(nid),
            nid,
        )
        .unwrap();
    }
    writeln!(file, "            Self::Unknown(s) => s,").unwrap();
    writeln!(file, "        }})").unwrap();
    writeln!(file, "    }}").unwrap();
    writeln!(file, "}}").unwrap();
}
