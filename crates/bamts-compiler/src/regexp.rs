use std::collections::BTreeSet;

const BINARY_PROPS: &[&str] = &[
    "AHex",
    "ASCII",
    "ASCII_Hex_Digit",
    "Alpha",
    "Alphabetic",
    "Any",
    "Assigned",
    "Bidi_C",
    "Bidi_Control",
    "Bidi_M",
    "Bidi_Mirrored",
    "CI",
    "CWCF",
    "CWCM",
    "CWKCF",
    "CWL",
    "CWT",
    "CWU",
    "Case_Ignorable",
    "Cased",
    "Changes_When_Casefolded",
    "Changes_When_Casemapped",
    "Changes_When_Lowercased",
    "Changes_When_NFKC_Casefolded",
    "Changes_When_Titlecased",
    "Changes_When_Uppercased",
    "DI",
    "Dash",
    "Default_Ignorable_Code_Point",
    "Dep",
    "Deprecated",
    "Dia",
    "Diacritic",
    "EBase",
    "EComp",
    "EMod",
    "EPres",
    "Emoji",
    "Emoji_Component",
    "Emoji_Modifier",
    "Emoji_Modifier_Base",
    "Emoji_Presentation",
    "Ext",
    "ExtPict",
    "Extended_Pictographic",
    "Extender",
    "Gr_Base",
    "Gr_Ext",
    "Grapheme_Base",
    "Grapheme_Extend",
    "Hex",
    "Hex_Digit",
    "IDC",
    "IDS",
    "IDSB",
    "IDST",
    "IDS_Binary_Operator",
    "IDS_Trinary_Operator",
    "ID_Continue",
    "ID_Start",
    "Ideo",
    "Ideographic",
    "Join_C",
    "Join_Control",
    "LOE",
    "Logical_Order_Exception",
    "Lower",
    "Lowercase",
    "Math",
    "NChar",
    "Noncharacter_Code_Point",
    "Pat_Syn",
    "Pat_WS",
    "Pattern_Syntax",
    "Pattern_White_Space",
    "QMark",
    "Quotation_Mark",
    "RI",
    "Radical",
    "Regional_Indicator",
    "SD",
    "STerm",
    "Sentence_Terminal",
    "Soft_Dotted",
    "Term",
    "Terminal_Punctuation",
    "UIdeo",
    "Unified_Ideograph",
    "Upper",
    "Uppercase",
    "VS",
    "Variation_Selector",
    "White_Space",
    "XIDC",
    "XIDS",
    "XID_Continue",
    "XID_Start",
    "space",
];
const GC_VALUES: &[&str] = &[
    "C",
    "Cased_Letter",
    "Cc",
    "Cf",
    "Close_Punctuation",
    "Cn",
    "Co",
    "Combining_Mark",
    "Connector_Punctuation",
    "Control",
    "Cs",
    "Currency_Symbol",
    "Dash_Punctuation",
    "Decimal_Number",
    "Enclosing_Mark",
    "Final_Punctuation",
    "Format",
    "Initial_Punctuation",
    "L",
    "LC",
    "Letter",
    "Letter_Number",
    "Line_Separator",
    "Ll",
    "Lm",
    "Lo",
    "Lowercase_Letter",
    "Lt",
    "Lu",
    "M",
    "Mark",
    "Math_Symbol",
    "Mc",
    "Me",
    "Mn",
    "Modifier_Letter",
    "Modifier_Symbol",
    "N",
    "Nd",
    "Nl",
    "No",
    "Nonspacing_Mark",
    "Number",
    "Open_Punctuation",
    "Other",
    "Other_Letter",
    "Other_Number",
    "Other_Punctuation",
    "Other_Symbol",
    "P",
    "Paragraph_Separator",
    "Pc",
    "Pd",
    "Pe",
    "Pf",
    "Pi",
    "Po",
    "Private_Use",
    "Ps",
    "Punctuation",
    "S",
    "Sc",
    "Separator",
    "Sk",
    "Sm",
    "So",
    "Space_Separator",
    "Spacing_Mark",
    "Surrogate",
    "Symbol",
    "Titlecase_Letter",
    "Unassigned",
    "Uppercase_Letter",
    "Z",
    "Zl",
    "Zp",
    "Zs",
    "cntrl",
    "digit",
    "punct",
];
const SC_VALUES: &[&str] = &[
    "Adlam",
    "Adlm",
    "Aghb",
    "Ahom",
    "Anatolian_Hieroglyphs",
    "Arab",
    "Arabic",
    "Armenian",
    "Armi",
    "Armn",
    "Avestan",
    "Avst",
    "Bali",
    "Balinese",
    "Bamu",
    "Bamum",
    "Bass",
    "Bassa_Vah",
    "Batak",
    "Batk",
    "Beng",
    "Bengali",
    "Bhaiksuki",
    "Bhks",
    "Bopo",
    "Bopomofo",
    "Brah",
    "Brahmi",
    "Brai",
    "Braille",
    "Bugi",
    "Buginese",
    "Buhd",
    "Buhid",
    "Cakm",
    "Canadian_Aboriginal",
    "Cans",
    "Cari",
    "Carian",
    "Caucasian_Albanian",
    "Chakma",
    "Cham",
    "Cher",
    "Cherokee",
    "Chorasmian",
    "Chrs",
    "Common",
    "Copt",
    "Coptic",
    "Cpmn",
    "Cprt",
    "Cuneiform",
    "Cypriot",
    "Cypro_Minoan",
    "Cyrillic",
    "Cyrl",
    "Deseret",
    "Deva",
    "Devanagari",
    "Diak",
    "Dives_Akuru",
    "Dogr",
    "Dogra",
    "Dsrt",
    "Dupl",
    "Duployan",
    "Egyp",
    "Egyptian_Hieroglyphs",
    "Elba",
    "Elbasan",
    "Elym",
    "Elymaic",
    "Ethi",
    "Ethiopic",
    "Gara",
    "Garay",
    "Geor",
    "Georgian",
    "Glag",
    "Glagolitic",
    "Gong",
    "Gonm",
    "Goth",
    "Gothic",
    "Gran",
    "Grantha",
    "Greek",
    "Grek",
    "Gujarati",
    "Gujr",
    "Gukh",
    "Gunjala_Gondi",
    "Gurmukhi",
    "Guru",
    "Gurung_Khema",
    "Han",
    "Hang",
    "Hangul",
    "Hani",
    "Hanifi_Rohingya",
    "Hano",
    "Hanunoo",
    "Hatr",
    "Hatran",
    "Hebr",
    "Hebrew",
    "Hira",
    "Hiragana",
    "Hluw",
    "Hmng",
    "Hmnp",
    "Hrkt",
    "Hung",
    "Imperial_Aramaic",
    "Inherited",
    "Inscriptional_Pahlavi",
    "Inscriptional_Parthian",
    "Ital",
    "Java",
    "Javanese",
    "Kaithi",
    "Kali",
    "Kana",
    "Kannada",
    "Katakana",
    "Katakana_Or_Hiragana",
    "Kawi",
    "Kayah_Li",
    "Khar",
    "Kharoshthi",
    "Khitan_Small_Script",
    "Khmer",
    "Khmr",
    "Khoj",
    "Khojki",
    "Khudawadi",
    "Kirat_Rai",
    "Kits",
    "Knda",
    "Krai",
    "Kthi",
    "Lana",
    "Lao",
    "Laoo",
    "Latin",
    "Latn",
    "Lepc",
    "Lepcha",
    "Limb",
    "Limbu",
    "Lina",
    "Linb",
    "Linear_A",
    "Linear_B",
    "Lisu",
    "Lyci",
    "Lycian",
    "Lydi",
    "Lydian",
    "Mahajani",
    "Mahj",
    "Maka",
    "Makasar",
    "Malayalam",
    "Mand",
    "Mandaic",
    "Mani",
    "Manichaean",
    "Marc",
    "Marchen",
    "Masaram_Gondi",
    "Medefaidrin",
    "Medf",
    "Meetei_Mayek",
    "Mend",
    "Mende_Kikakui",
    "Merc",
    "Mero",
    "Meroitic_Cursive",
    "Meroitic_Hieroglyphs",
    "Miao",
    "Mlym",
    "Modi",
    "Mong",
    "Mongolian",
    "Mro",
    "Mroo",
    "Mtei",
    "Mult",
    "Multani",
    "Myanmar",
    "Mymr",
    "Nabataean",
    "Nag_Mundari",
    "Nagm",
    "Nand",
    "Nandinagari",
    "Narb",
    "Nbat",
    "New_Tai_Lue",
    "Newa",
    "Nko",
    "Nkoo",
    "Nshu",
    "Nushu",
    "Nyiakeng_Puachue_Hmong",
    "Ogam",
    "Ogham",
    "Ol_Chiki",
    "Ol_Onal",
    "Olck",
    "Old_Hungarian",
    "Old_Italic",
    "Old_North_Arabian",
    "Old_Permic",
    "Old_Persian",
    "Old_Sogdian",
    "Old_South_Arabian",
    "Old_Turkic",
    "Old_Uyghur",
    "Onao",
    "Oriya",
    "Orkh",
    "Orya",
    "Osage",
    "Osge",
    "Osma",
    "Osmanya",
    "Ougr",
    "Pahawh_Hmong",
    "Palm",
    "Palmyrene",
    "Pau_Cin_Hau",
    "Pauc",
    "Perm",
    "Phag",
    "Phags_Pa",
    "Phli",
    "Phlp",
    "Phnx",
    "Phoenician",
    "Plrd",
    "Prti",
    "Psalter_Pahlavi",
    "Qaac",
    "Qaai",
    "Rejang",
    "Rjng",
    "Rohg",
    "Runic",
    "Runr",
    "Samaritan",
    "Samr",
    "Sarb",
    "Saur",
    "Saurashtra",
    "Sgnw",
    "Sharada",
    "Shavian",
    "Shaw",
    "Shrd",
    "Sidd",
    "Siddham",
    "SignWriting",
    "Sind",
    "Sinh",
    "Sinhala",
    "Sogd",
    "Sogdian",
    "Sogo",
    "Sora",
    "Sora_Sompeng",
    "Soyo",
    "Soyombo",
    "Sund",
    "Sundanese",
    "Sunu",
    "Sunuwar",
    "Sylo",
    "Syloti_Nagri",
    "Syrc",
    "Syriac",
    "Tagalog",
    "Tagb",
    "Tagbanwa",
    "Tai_Le",
    "Tai_Tham",
    "Tai_Viet",
    "Takr",
    "Takri",
    "Tale",
    "Talu",
    "Tamil",
    "Taml",
    "Tang",
    "Tangsa",
    "Tangut",
    "Tavt",
    "Telu",
    "Telugu",
    "Tfng",
    "Tglg",
    "Thaa",
    "Thaana",
    "Thai",
    "Tibetan",
    "Tibt",
    "Tifinagh",
    "Tirh",
    "Tirhuta",
    "Tnsa",
    "Todhri",
    "Todr",
    "Toto",
    "Tulu_Tigalari",
    "Tutg",
    "Ugar",
    "Ugaritic",
    "Unknown",
    "Vai",
    "Vaii",
    "Vith",
    "Vithkuqi",
    "Wancho",
    "Wara",
    "Warang_Citi",
    "Wcho",
    "Xpeo",
    "Xsux",
    "Yezi",
    "Yezidi",
    "Yi",
    "Yiii",
    "Zanabazar_Square",
    "Zanb",
    "Zinh",
    "Zyyy",
    "Zzzz",
];
const STRING_PROPS: &[&str] = &[
    "Basic_Emoji",
    "Emoji_Keycap_Sequence",
    "RGI_Emoji",
    "RGI_Emoji_Flag_Sequence",
    "RGI_Emoji_Modifier_Sequence",
    "RGI_Emoji_Tag_Sequence",
    "RGI_Emoji_ZWJ_Sequence",
];
const TABLE65_NAMES: &[&str] = &["General_Category", "Script", "Script_Extensions", "gc", "sc", "scx"];

#[derive(Clone, Copy)]
enum RegexMode {
    Legacy,
    Unicode,
    UnicodeSets,
}

pub fn validate_regex_literal(literal: &str) -> Option<String> {
    let (head, flags) = literal.rsplit_once('/')?;
    let pattern = head.strip_prefix('/')?;
    let pattern_units: Vec<u16> = pattern.encode_utf16().collect();
    let flag_units: Vec<u16> = flags.encode_utf16().collect();
    if let Some(message) = validate_flags(&flag_units) {
        return Some(message);
    }
    validate_pattern(&pattern_units, mode_for_flags(flags))
}

fn mode_for_flags(flags: &str) -> RegexMode {
    if flags.contains('v') {
        RegexMode::UnicodeSets
    } else if flags.contains('u') {
        RegexMode::Unicode
    } else {
        RegexMode::Legacy
    }
}

fn validate_flags(flags: &[u16]) -> Option<String> {
    let mut seen = BTreeSet::new();
    for &unit in flags {
        let flag = u32::from(unit);
        let valid = matches!(flag, 0x64 | 0x67 | 0x69 | 0x6D | 0x73 | 0x75 | 0x76 | 0x79);
        if !valid {
            return Some(format!("invalid regular expression flag"));
        }
        if !seen.insert(unit) {
            return Some(format!("duplicate regular expression flag"));
        }
    }
    if seen.contains(&0x75) && seen.contains(&0x76) {
        return Some(format!("regular expression flags `u` and `v` cannot be combined"));
    }
    None
}

fn validate_pattern(pattern: &[u16], mode: RegexMode) -> Option<String> {
    let mut parser = Parser {
        units: pattern,
        pos: 0,
        mode,
    };
    parser.parse_top()
}

struct Parser<'a> {
    units: &'a [u16],
    pos: usize,
    mode: RegexMode,
}

impl<'a> Parser<'a> {
    fn peek(&self) -> Option<u16> {
        self.units.get(self.pos).copied()
    }

    fn peek_at(&self, offset: usize) -> Option<u16> {
        self.units.get(self.pos + offset).copied()
    }

    fn parse_top(&mut self) -> Option<String> {
        if let Some(message) = self.parse_disjunction() {
            return Some(message);
        }
        if self.pos != self.units.len() {
            return Some(format!("invalid regular expression"));
        }
        None
    }

    fn parse_disjunction(&mut self) -> Option<String> {
        loop {
            if let Some(message) = self.parse_alternative() {
                return Some(message);
            }
            if self.peek() == Some(0x7C) {
                self.pos += 1;
                continue;
            }
            return None;
        }
    }

    fn parse_alternative(&mut self) -> Option<String> {
        loop {
            match self.peek() {
                None | Some(0x7C) | Some(0x29) => return None,
                _ => {}
            }
            if let Some(message) = self.parse_term() {
                return Some(message);
            }
        }
    }

    fn parse_term(&mut self) -> Option<String> {
        match self.peek() {
            Some(0x28) => self.parse_group(),
            Some(0x5B) => self.parse_class(),
            Some(0x5C) => self.parse_escape(),
            Some(0x29) => Some(format!("invalid regular expression")),
            None => None,
            _ => {
                self.pos += 1;
                self.skip_quantifier();
                None
            }
        }
    }

    fn skip_quantifier(&mut self) {
        match self.peek() {
            Some(0x2A) | Some(0x2B) | Some(0x3F) => {
                self.pos += 1;
                if self.peek() == Some(0x3F) {
                    self.pos += 1;
                }
            }
            Some(0x7B) => {
                let start = self.pos;
                self.pos += 1;
                let mut digits = 0;
                while matches!(self.peek(), Some(0x30..=0x39)) {
                    self.pos += 1;
                    digits += 1;
                }
                if digits == 0 {
                    self.pos = start;
                    return;
                }
                if self.peek() == Some(0x2C) {
                    self.pos += 1;
                    while matches!(self.peek(), Some(0x30..=0x39)) {
                        self.pos += 1;
                    }
                }
                if self.peek() != Some(0x7D) {
                    self.pos = start;
                    return;
                }
                self.pos += 1;
                if self.peek() == Some(0x3F) {
                    self.pos += 1;
                }
            }
            _ => {}
        }
    }

    fn parse_group(&mut self) -> Option<String> {
        self.pos += 1;
        if self.peek() != Some(0x3F) {
            if let Some(message) = self.parse_disjunction() {
                return Some(message);
            }
            if self.peek() != Some(0x29) {
                return Some(format!("invalid regular expression"));
            }
            self.pos += 1;
            self.skip_quantifier();
            return None;
        }
        self.pos += 1;
        match self.peek() {
            Some(0x3A) => {
                self.pos += 1;
                if let Some(message) = self.parse_disjunction() {
                    return Some(message);
                }
                if self.peek() != Some(0x29) {
                    return Some(format!("invalid regular expression"));
                }
                self.pos += 1;
                self.skip_quantifier();
                None
            }
            Some(0x3D) | Some(0x21) => {
                self.pos += 1;
                if let Some(message) = self.parse_disjunction() {
                    return Some(message);
                }
                if self.peek() != Some(0x29) {
                    return Some(format!("invalid regular expression"));
                }
                self.pos += 1;
                self.skip_quantifier();
                None
            }
            Some(0x3C) => {
                if matches!(self.peek_at(1), Some(0x3D) | Some(0x21)) {
                    self.pos += 2;
                    if let Some(message) = self.parse_disjunction() {
                        return Some(message);
                    }
                    if self.peek() != Some(0x29) {
                        return Some(format!("invalid regular expression"));
                    }
                    self.pos += 1;
                    self.skip_quantifier();
                    return None;
                }
                self.parse_named_group()
            }
            _ => self.parse_modifiers(),
        }
    }

    fn parse_named_group(&mut self) -> Option<String> {
        self.pos += 1;
        while let Some(unit) = self.peek() {
            if unit == 0x3E {
                self.pos += 1;
                break;
            }
            if unit == 0x29 || unit == 0x2F {
                return Some(format!("invalid regular expression"));
            }
            self.pos += 1;
        }
        if let Some(message) = self.parse_disjunction() {
            return Some(message);
        }
        if self.peek() != Some(0x29) {
            return Some(format!("invalid regular expression"));
        }
        self.pos += 1;
        self.skip_quantifier();
        None
    }

    fn parse_modifiers(&mut self) -> Option<String> {
        let first_start = self.pos;
        while let Some(unit) = self.peek() {
            if unit == 0x2D || unit == 0x3A || unit == 0x29 {
                break;
            }
            self.pos += 1;
        }
        let first: Vec<u16> = self.units[first_start..self.pos].to_vec();
        let mut second = Vec::new();
        let has_dash = self.peek() == Some(0x2D);
        if has_dash {
            self.pos += 1;
            let second_start = self.pos;
            while let Some(unit) = self.peek() {
                if unit == 0x3A || unit == 0x29 {
                    break;
                }
                self.pos += 1;
            }
            second = self.units[second_start..self.pos].to_vec();
        }
        if self.peek() != Some(0x3A) {
            return Some(format!("invalid regular expression"));
        }
        if has_dash {
            if let Some(message) = validate_paired_modifiers(&first, &second) {
                return Some(message);
            }
        } else if let Some(message) = validate_single_modifier(&first) {
            return Some(message);
        }
        self.pos += 1;
        if let Some(message) = self.parse_disjunction() {
            return Some(message);
        }
        if self.peek() != Some(0x29) {
            return Some(format!("invalid regular expression"));
        }
        self.pos += 1;
        self.skip_quantifier();
        None
    }
    fn parse_class(&mut self) -> Option<String> {
        self.pos += 1;
        if self.peek() == Some(0x5E) {
            self.pos += 1;
        }
        if matches!(self.mode, RegexMode::UnicodeSets) {
            return self.parse_class_sets();
        }
        loop {
            match self.peek() {
                None => return Some(format!("invalid regular expression")),
                Some(0x5D) => {
                    self.pos += 1;
                    break;
                }
                Some(0x5C) if self.is_property_prefix() => {
                    if let Some(message) = self.parse_property_escape() {
                        return Some(message);
                    }
                }
                Some(0x5C) => {
                    self.pos += 1;
                    if self.peek().is_none() {
                        return Some(format!("invalid regular expression"));
                    }
                    self.pos += 1;
                }
                _ => {
                    self.pos += 1;
                }
            }
        }
        self.skip_quantifier();
        None
    }

    fn parse_class_sets(&mut self) -> Option<String> {
        let mut depth = 1;
        loop {
            match self.peek() {
                None => return Some(format!("invalid regular expression")),
                Some(0x5D) => {
                    self.pos += 1;
                    depth -= 1;
                    if depth == 0 {
                        break;
                    }
                }
                Some(0x5B) => {
                    self.pos += 1;
                    depth += 1;
                }
                Some(0x5C) if self.is_property_prefix() => {
                    if let Some(message) = self.parse_property_escape() {
                        return Some(message);
                    }
                }
                Some(0x5C) => {
                    self.pos += 1;
                    if self.peek().is_none() {
                        return Some(format!("invalid regular expression"));
                    }
                    self.pos += 1;
                }
                _ => {
                    self.pos += 1;
                }
            }
        }
        self.skip_quantifier();
        None
    }

    fn parse_escape(&mut self) -> Option<String> {
        if self.is_property_prefix() {
            if let Some(message) = self.parse_property_escape() {
                return Some(message);
            }
            self.skip_quantifier();
            return None;
        }
        self.pos += 1;
        if self.peek().is_none() {
            return Some(format!("invalid regular expression"));
        }
        self.pos += 1;
        self.skip_quantifier();
        None
    }

    fn is_property_prefix(&self) -> bool {
        if !matches!(self.mode, RegexMode::Unicode | RegexMode::UnicodeSets) {
            return false;
        }
        if self.units.get(self.pos) != Some(&0x5C) {
            return false;
        }
        matches!(self.units.get(self.pos + 1), Some(0x70) | Some(0x50))
    }

    fn parse_property_escape(&mut self) -> Option<String> {
        self.pos += 2;
        if self.peek() != Some(0x7B) {
            return Some(format!("invalid regular expression"));
        }
        self.pos += 1;
        let content_start = self.pos;
        while self.peek() != Some(0x7D) {
            if self.peek().is_none() {
                return Some(format!("invalid regular expression"));
            }
            self.pos += 1;
        }
        let content = &self.units[content_start..self.pos];
        if let Some(message) = validate_property_content(content, self.mode) {
            return Some(message);
        }
        self.pos += 1;
        None
    }
}


fn units_eq_str(units: &[u16], text: &str) -> bool {
    if units.len() != text.len() {
        return false;
    }
    units.iter().zip(text.bytes()).all(|(unit, byte)| *unit == u16::from(byte))
}

fn is_property_char(unit: u16) -> bool {
    matches!(unit, 0x30..=0x39 | 0x41..=0x5A | 0x5F | 0x61..=0x7A)
}

fn validate_property_content(content: &[u16], mode: RegexMode) -> Option<String> {
    if content.is_empty() {
        return Some(format!("invalid regular expression"));
    }
    if content.iter().any(|unit| *unit > 0x7F) {
        return Some(format!("invalid regular expression"));
    }
    if content.iter().any(|unit| !is_property_char(*unit) && *unit != 0x3D) {
        return Some(format!("invalid regular expression"));
    }
    let equals = content.iter().filter(|unit| **unit == 0x3D).count();
    if equals > 1 {
        return Some(format!("invalid regular expression"));
    }
    if equals == 0 {
        return validate_lone_property(content, mode);
    }
    let split = content.iter().position(|unit| *unit == 0x3D);
    match split {
        Some(idx) => validate_named_property(&content[..idx], &content[idx + 1..]),
        None => Some(format!("invalid regular expression")),
    }
}

fn validate_lone_property(content: &[u16], mode: RegexMode) -> Option<String> {
    if GC_VALUES.iter().any(|cand| units_eq_str(content, cand)) {
        return None;
    }
    if BINARY_PROPS.iter().any(|cand| units_eq_str(content, cand)) {
        return None;
    }
    if STRING_PROPS.iter().any(|cand| units_eq_str(content, cand)) {
        if matches!(mode, RegexMode::UnicodeSets) {
            return None;
        }
        return Some(format!("invalid regular expression"));
    }
    Some(format!("invalid regular expression"))
}

fn validate_named_property(name: &[u16], value: &[u16]) -> Option<String> {
    if name.is_empty() || value.is_empty() {
        return Some(format!("invalid regular expression"));
    }
    if name.iter().any(|unit| !is_property_char(*unit)) {
        return Some(format!("invalid regular expression"));
    }
    if value.iter().any(|unit| !is_property_char(*unit)) {
        return Some(format!("invalid regular expression"));
    }
    if !TABLE65_NAMES.iter().any(|cand| units_eq_str(name, cand)) {
        return Some(format!("invalid regular expression"));
    }
    if units_eq_str(name, "General_Category") || units_eq_str(name, "gc") {
        if GC_VALUES.iter().any(|cand| units_eq_str(value, cand)) {
            return None;
        }
        return Some(format!("invalid regular expression"));
    }
    if SC_VALUES.iter().any(|cand| units_eq_str(value, cand)) {
        return None;
    }
    Some(format!("invalid regular expression"))
}

fn validate_single_modifier(first: &[u16]) -> Option<String> {
    if first.is_empty() {
        return Some(format!("invalid regular expression"));
    }
    check_modifier_list(first).map(|_| format!("invalid regular expression"))
}

fn validate_paired_modifiers(first: &[u16], second: &[u16]) -> Option<String> {
    if first.is_empty() && second.is_empty() {
        return Some(format!("invalid regular expression"));
    }
    if check_modifier_list(first).is_some() {
        return Some(format!("invalid regular expression"));
    }
    if check_modifier_list(second).is_some() {
        return Some(format!("invalid regular expression"));
    }
    if first.iter().any(|unit| second.contains(unit)) {
        return Some(format!("invalid regular expression"));
    }
    None
}

fn check_modifier_list(flags: &[u16]) -> Option<()> {
    if flags.iter().any(|unit| !matches!(unit, 0x69 | 0x6D | 0x73)) {
        return Some(());
    }
    let mut seen = BTreeSet::new();
    for unit in flags {
        if !seen.insert(unit) {
            return Some(());
        }
    }
    None
}
