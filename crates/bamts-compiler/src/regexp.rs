use std::collections::BTreeSet;
use crate::scanner::{is_id_continue, is_id_start};

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
        disjunctions: Vec::new(),
        next_disjunction: 0,
        groups: Vec::new(),
        references: Vec::new(),
        bare_k: 0,
        incomplete_k: 0,
        captures: 0,
        decimals: Vec::new(),
    };
    parser.parse_top()
}

struct GroupDef {
    name: Vec<u16>,
    context: Vec<(usize, usize)>,
}
enum ClassAtom {
    Single(u32),
    Multi,
}

impl ClassAtom {
    fn range_valid(first: &ClassAtom, second: &ClassAtom) -> bool {
        match (first, second) {
            (ClassAtom::Single(low), ClassAtom::Single(high)) => low <= high,
            _ => false,
        }
    }
}

struct Parser<'a> {
    units: &'a [u16],
    pos: usize,
    mode: RegexMode,
    disjunctions: Vec<(usize, usize)>,
    next_disjunction: usize,
    groups: Vec<GroupDef>,
    references: Vec<Vec<u16>>,
    bare_k: usize,
    incomplete_k: usize,
    captures: usize,
    decimals: Vec<usize>,
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
        if let Some(message) = self.check_named_groups() {
            return Some(message);
        }
        self.check_decimals()
    }

    fn parse_disjunction(&mut self) -> Option<String> {
        let id = self.next_disjunction;
        self.next_disjunction += 1;
        self.disjunctions.push((id, 0));
        loop {
            if let Some(message) = self.parse_alternative() {
                return Some(message);
            }
            if self.peek() == Some(0x7C) {
                self.pos += 1;
                if let Some(top) = self.disjunctions.last_mut() {
                    top.1 += 1;
                }
                continue;
            }
            break;
        }
        self.disjunctions.pop();
        None
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
            Some(0x7B) if is_braced_quantifier_at(self.units, self.pos) => {
                Some(format!("invalid regular expression"))
            }
            _ => {
                if matches!(self.mode, RegexMode::Unicode | RegexMode::UnicodeSets)
                    && matches!(self.peek(), Some(0x7B) | Some(0x7D) | Some(0x5D))
                {
                    return Some(format!("invalid regular expression"));
                }
                self.pos += 1;
                if let Some(message) = self.skip_quantifier() { return Some(message); }
                None
            }
        }
    }

    fn skip_quantifier(&mut self) -> Option<String> {
        match self.peek() {
            Some(0x2A) | Some(0x2B) | Some(0x3F) => {
                self.pos += 1;
                if self.peek() == Some(0x3F) {
                    self.pos += 1;
                }
                None
            }
            Some(0x7B) => self.skip_braced_quantifier(),
            _ => None,
        }
    }

    fn skip_braced_quantifier(&mut self) -> Option<String> {
        let start = self.pos;
        self.pos += 1;
        let first = self.parse_quantifier_number();
        if first.is_none() {
            self.pos = start;
            return None;
        }
        let low = first.unwrap_or(0);
        let mut high = Some(low);
        if self.peek() == Some(0x2C) {
            self.pos += 1;
            high = self.parse_quantifier_number();
        }
        if self.peek() != Some(0x7D) {
            self.pos = start;
            return None;
        }
        self.pos += 1;
        if self.peek() == Some(0x3F) {
            self.pos += 1;
        }
        if let Some(hi) = high {
            if hi < low && matches!(self.mode, RegexMode::Unicode | RegexMode::UnicodeSets) {
                return Some(format!("invalid regular expression"));
            }
        }
        None
    }

    fn parse_quantifier_number(&mut self) -> Option<usize> {
        let mut value: usize = 0;
        let mut digits = 0;
        while let Some(unit) = self.peek() {
            if !(0x30..=0x39).contains(&unit) {
                break;
            }
            value = value.saturating_mul(10).saturating_add((unit - 0x30) as usize);
            self.pos += 1;
            digits += 1;
        }
        if digits == 0 {
            return None;
        }
        Some(value)
    }

    fn is_quantifier_ahead(&self) -> bool {
        match self.peek() {
            Some(0x2A) | Some(0x2B) | Some(0x3F) => true,
            Some(0x7B) => is_braced_quantifier_at(self.units, self.pos),
            _ => false,
        }
    }

    fn parse_group(&mut self) -> Option<String> {
        self.pos += 1;
        if self.peek() != Some(0x3F) {
            self.captures += 1;
            if let Some(message) = self.parse_disjunction() {
                return Some(message);
            }
            if self.peek() != Some(0x29) {
                return Some(format!("invalid regular expression"));
            }
            self.pos += 1;
            if let Some(message) = self.skip_quantifier() { return Some(message); }
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
                if let Some(message) = self.skip_quantifier() { return Some(message); }
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
                if matches!(self.mode, RegexMode::Unicode | RegexMode::UnicodeSets)
                    && self.is_quantifier_ahead()
                {
                    return Some(format!("invalid regular expression"));
                }
                if let Some(message) = self.skip_quantifier() { return Some(message); }
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
                    if self.is_quantifier_ahead() {
                        return Some(format!("invalid regular expression"));
                    }
                    if let Some(message) = self.skip_quantifier() { return Some(message); }
                    return None;
                }
                self.parse_named_group()
            }
            _ => self.parse_modifiers(),
        }
    }

    fn parse_named_group(&mut self) -> Option<String> {
        self.pos += 1;
        let name_start = self.pos;
        while let Some(unit) = self.peek() {
            if unit == 0x3E {
                break;
            }
            if unit == 0x29 || unit == 0x2F {
                return Some(format!("invalid regular expression"));
            }
            if unit == 0x5C {
                break;
            }
            self.pos += 1;
        }
        if self.peek() == Some(0x5C) {
            return self.parse_named_group_escaped(name_start);
        }
        let name: Vec<u16> = self.units[name_start..self.pos].to_vec();
        if name.is_empty() {
            return Some(format!("invalid regular expression"));
        }
        if let Some(message) = validate_group_name(&name) {
            return Some(message);
        }
        if self.peek() != Some(0x3E) {
            return Some(format!("invalid regular expression"));
        }
        self.pos += 1;
        self.groups.push(GroupDef {
            name,
            context: self.disjunctions.clone(),
        });
        self.captures += 1;
        if let Some(message) = self.parse_disjunction() {
            return Some(message);
        }
        if self.peek() != Some(0x29) {
            return Some(format!("invalid regular expression"));
        }
        self.pos += 1;
        if let Some(message) = self.skip_quantifier() { return Some(message); }
        None
    }

    fn parse_named_group_escaped(&mut self, name_start: usize) -> Option<String> {
        while let Some(unit) = self.peek() {
            if unit == 0x3E {
                break;
            }
            if unit == 0x29 || unit == 0x2F {
                return Some(format!("invalid regular expression"));
            }
            if unit == 0x5C {
                self.pos += 1;
                if self.peek().is_none() {
                    return Some(format!("invalid regular expression"));
                }
                self.pos += 1;
                continue;
            }
            self.pos += 1;
        }
        if self.peek() != Some(0x3E) {
            return Some(format!("invalid regular expression"));
        }
        let name: Vec<u16> = self.units[name_start..self.pos].to_vec();
        if name.is_empty() {
            return Some(format!("invalid regular expression"));
        }
        if let Some(message) = validate_group_name(&name) {
            return Some(message);
        }
        self.pos += 1;
        self.groups.push(GroupDef {
            name,
            context: self.disjunctions.clone(),
        });
        self.captures += 1;
        if let Some(message) = self.parse_disjunction() {
            return Some(message);
        }
        if self.peek() != Some(0x29) {
            return Some(format!("invalid regular expression"));
        }
        self.pos += 1;
        if let Some(message) = self.skip_quantifier() { return Some(message); }
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
        if let Some(message) = self.skip_quantifier() { return Some(message); }
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
        if matches!(self.mode, RegexMode::Unicode) {
            return self.parse_class_unicode();
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
        if let Some(message) = self.skip_quantifier() { return Some(message); }
        None
    }

    fn parse_class_unicode(&mut self) -> Option<String> {
        loop {
            match self.peek() {
                None => return Some(format!("invalid regular expression")),
                Some(0x5D) => {
                    self.pos += 1;
                    break;
                }
                _ => {
                    let Some(first) = self.parse_class_atom_unicode() else {
                        return Some(format!("invalid regular expression"));
                    };
                    if self.peek() == Some(0x2D) && self.units.get(self.pos + 1) != Some(&0x5D) {
                        self.pos += 1;
                        let Some(second) = self.parse_class_atom_unicode() else {
                            return Some(format!("invalid regular expression"));
                        };
                        if !ClassAtom::range_valid(&first, &second) {
                            return Some(format!("invalid regular expression"));
                        }
                    }
                }
            }
        }
        if let Some(message) = self.skip_quantifier() { return Some(message); }
        None
    }

    fn parse_class_atom_unicode(&mut self) -> Option<ClassAtom> {
        match self.peek() {
            Some(0x5C) => {
                let escaped = self.units.get(self.pos + 1).copied()?;
                match escaped {
                    0x62 => {
                        self.pos += 2;
                        Some(ClassAtom::Single(0x08))
                    }
                    0x66 => {
                        self.pos += 2;
                        Some(ClassAtom::Single(0x0C))
                    }
                    0x6E => {
                        self.pos += 2;
                        Some(ClassAtom::Single(0x0A))
                    }
                    0x72 => {
                        self.pos += 2;
                        Some(ClassAtom::Single(0x0D))
                    }
                    0x74 => {
                        self.pos += 2;
                        Some(ClassAtom::Single(0x09))
                    }
                    0x76 => {
                        self.pos += 2;
                        Some(ClassAtom::Single(0x0B))
                    }
                    0x63 => {
                        let letter = self.units.get(self.pos + 2).copied()?;
                        if !matches!(letter, 0x41..=0x5A | 0x61..=0x7A) {
                            return None;
                        }
                        self.pos += 3;
                        Some(ClassAtom::Single(u32::from(letter) & 31))
                    }
                    0x78 => {
                        let high = self.units.get(self.pos + 2).copied()?;
                        let low = self.units.get(self.pos + 3).copied()?;
                        if !is_hex_digit(high) || !is_hex_digit(low) {
                            return None;
                        }
                        self.pos += 4;
                        Some(ClassAtom::Single(hex_value(high) * 16 + hex_value(low)))
                    }
                    0x75 => self.parse_class_unicode_escape(),
                    0x30 => {
                        if matches!(self.units.get(self.pos + 2).copied(), Some(0x30..=0x39)) {
                            return None;
                        }
                        self.pos += 2;
                        Some(ClassAtom::Single(0))
                    }
                    0x31..=0x39 => {
                        let mut idx = self.pos + 1;
                        let mut value: usize = 0;
                        while idx < self.units.len() && (0x30..=0x39).contains(&self.units[idx]) {
                            value = value.saturating_mul(10).saturating_add(usize::from(self.units[idx] - 0x30));
                            idx += 1;
                        }
                        self.decimals.push(value);
                        self.pos = idx;
                        Some(ClassAtom::Multi)
                    }
                    0x64 | 0x44 | 0x77 | 0x57 | 0x73 | 0x53 => {
                        self.pos += 2;
                        Some(ClassAtom::Multi)
                    }
                    0x70 | 0x50 => {
                        if self.parse_property_escape().is_some() {
                            return None;
                        }
                        Some(ClassAtom::Multi)
                    }
                    0x6B => {
                        self.parse_k_reference();
                        Some(ClassAtom::Multi)
                    }
                    _ if is_valid_u_single(escaped, true) => {
                        self.pos += 2;
                        Some(ClassAtom::Single(u32::from(escaped)))
                    }
                    _ => None,
                }
            }
            Some(0x2D) => {
                self.pos += 1;
                Some(ClassAtom::Single(0x2D))
            }
            Some(unit) if (0xD800..0xDC00).contains(&unit) => {
                let low = self.units.get(self.pos + 1).copied()?;
                if !(0xDC00..0xE000).contains(&low) {
                    return None;
                }
                self.pos += 2;
                let value = 0x10000 + ((u32::from(unit - 0xD800)) << 10) + u32::from(low - 0xDC00);
                Some(ClassAtom::Single(value))
            }
            Some(unit) => {
                if (0xDC00..0xE000).contains(&unit) {
                    return None;
                }
                self.pos += 1;
                Some(ClassAtom::Single(u32::from(unit)))
            }
            None => None,
        }
    }

    fn parse_class_unicode_escape(&mut self) -> Option<ClassAtom> {
        if self.units.get(self.pos + 2).copied() == Some(0x7B) {
            let mut idx = self.pos + 3;
            let mut digits = 0;
            let mut value: u32 = 0;
            while idx < self.units.len() && self.units[idx] != 0x7D {
                if !is_hex_digit(self.units[idx]) {
                    return None;
                }
                value = value.saturating_mul(16).saturating_add(hex_value(self.units[idx]));
                idx += 1;
                digits += 1;
                if digits > 6 {
                    return None;
                }
            }
            if digits == 0 || idx >= self.units.len() {
                return None;
            }
            if value > 0x10FFFF || (0xD800..=0xDFFF).contains(&value) {
                return None;
            }
            self.pos = idx + 1;
            return Some(ClassAtom::Single(value));
        }
        let mut idx = self.pos + 2;
        let mut count = 0;
        let mut value: u32 = 0;
        while count < 4 {
            let unit = self.units.get(idx).copied()?;
            if !is_hex_digit(unit) {
                return None;
            }
            value = value * 16 + hex_value(unit);
            idx += 1;
            count += 1;
        }
        self.pos = idx;
        Some(ClassAtom::Single(value))
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
                Some(0x5C) if self.is_q_prefix() => {
                    if let Some(message) = self.parse_q_string() {
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
                Some(unit) if is_v_single_error(unit) => {
                    return Some(format!("invalid regular expression"));
                }
                Some(0x2D) if self.is_lone_dash_class(depth) => {
                    return Some(format!("invalid regular expression"));
                }
                Some(0x26) if self.is_lone_double_amp() => {
                    return Some(format!("invalid regular expression"));
                }
                Some(unit) if self.is_reserved_double_at(unit) => {
                    return Some(format!("invalid regular expression"));
                }
                _ => {
                    self.pos += 1;
                }
            }
        }
        if let Some(message) = self.skip_quantifier() { return Some(message); }
        None
    }

    fn is_q_prefix(&self) -> bool {
        self.units.get(self.pos) == Some(&0x5C) && self.units.get(self.pos + 1) == Some(&0x71)
    }

    fn parse_q_string(&mut self) -> Option<String> {
        self.pos += 2;
        if self.peek() != Some(0x7B) {
            return Some(format!("invalid regular expression"));
        }
        self.pos += 1;
        while let Some(unit) = self.peek() {
            if unit == 0x7D {
                self.pos += 1;
                return None;
            }
            self.pos += 1;
        }
        Some(format!("invalid regular expression"))
    }

    fn is_lone_dash_class(&self, depth: usize) -> bool {
        if depth != 1 {
            return false;
        }
        if self.units.get(self.pos) != Some(&0x2D) {
            return false;
        }
        let prev_is_open = self.pos >= 1 && self.units.get(self.pos - 1) == Some(&0x5B);
        let prev_is_caret_open = self.pos >= 2
            && self.units.get(self.pos - 2) == Some(&0x5B)
            && self.units.get(self.pos - 1) == Some(&0x5E);
        let next_is_close = self.units.get(self.pos + 1) == Some(&0x5D);
        next_is_close && (prev_is_open || prev_is_caret_open)
    }

    fn is_lone_double_amp(&self) -> bool {
        if self.units.get(self.pos) != Some(&0x26) {
            return false;
        }
        if self.units.get(self.pos + 1) != Some(&0x26) {
            return false;
        }
        let prev_is_open = self.pos >= 1 && self.units.get(self.pos - 1) == Some(&0x5B);
        let next_is_close = self.units.get(self.pos + 2) == Some(&0x5D);
        prev_is_open && next_is_close
    }

    fn is_reserved_double_at(&self, unit: u16) -> bool {
        let next = match self.units.get(self.pos + 1).copied() {
            Some(n) => n,
            None => return false,
        };
        if unit != next {
            return false;
        }
        matches!(
            unit,
            0x21 | 0x23 | 0x24 | 0x25 | 0x2A | 0x2B | 0x2C | 0x2E | 0x3A | 0x3B | 0x3C
                | 0x3D | 0x3E | 0x3F | 0x40 | 0x60 | 0x7E | 0x5E
        )
    }

    fn parse_escape(&mut self) -> Option<String> {
        if self.is_property_prefix() {
            if let Some(message) = self.parse_property_escape() {
                return Some(message);
            }
            if let Some(message) = self.skip_quantifier() { return Some(message); }
            return None;
        }
        if self.is_k_prefix() {
            self.parse_k_reference();
            if let Some(message) = self.skip_quantifier() { return Some(message); }
            return None;
        }
        if matches!(self.mode, RegexMode::Unicode | RegexMode::UnicodeSets) {
            return self.parse_u_escape(false);
        }
        self.pos += 1;
        if self.peek().is_none() {
            return Some(format!("invalid regular expression"));
        }
        self.pos += 1;
        if let Some(message) = self.skip_quantifier() { return Some(message); }
        None
    }

    fn parse_u_escape(&mut self, in_class: bool) -> Option<String> {
        let escaped = match self.units.get(self.pos + 1).copied() {
            Some(unit) => unit,
            None => return Some(format!("invalid regular expression")),
        };
        if escaped == 0x63 {
            return self.parse_control_escape();
        }
        if escaped == 0x78 {
            return self.parse_hex_escape();
        }
        if escaped == 0x75 {
            return self.parse_unicode_escape();
        }
        if escaped == 0x30 {
            if matches!(self.units.get(self.pos + 2).copied(), Some(0x30..=0x39)) {
                return Some(format!("invalid regular expression"));
            }
            self.pos += 2;
            if let Some(message) = self.skip_quantifier() { return Some(message); }
            return None;
        }
        if (0x31..=0x39).contains(&escaped) {
            return self.parse_decimal_escape();
        }
        if is_valid_u_single(escaped, in_class) {
            self.pos += 2;
            if let Some(message) = self.skip_quantifier() { return Some(message); }
            return None;
        }
        Some(format!("invalid regular expression"))
    }

    fn parse_control_escape(&mut self) -> Option<String> {
        match self.units.get(self.pos + 2).copied() {
            Some(0x41..=0x5A) | Some(0x61..=0x7A) => {
                self.pos += 3;
                if let Some(message) = self.skip_quantifier() { return Some(message); }
                None
            }
            _ => Some(format!("invalid regular expression")),
        }
    }

    fn parse_hex_escape(&mut self) -> Option<String> {
        let first = self.units.get(self.pos + 2).copied();
        let second = self.units.get(self.pos + 3).copied();
        match (first, second) {
            (Some(a), Some(b)) if is_hex_digit(a) && is_hex_digit(b) => {
                self.pos += 4;
                if let Some(message) = self.skip_quantifier() { return Some(message); }
                None
            }
            _ => Some(format!("invalid regular expression")),
        }
    }

    fn parse_unicode_escape(&mut self) -> Option<String> {
        if self.units.get(self.pos + 2).copied() == Some(0x7B) {
            return self.parse_unicode_braced_escape();
        }
        let mut idx = self.pos + 2;
        let mut count = 0;
        while count < 4 {
            match self.units.get(idx).copied() {
                Some(unit) if is_hex_digit(unit) => {
                    idx += 1;
                    count += 1;
                }
                _ => return Some(format!("invalid regular expression")),
            }
        }
        self.pos = idx;
        if let Some(message) = self.skip_quantifier() { return Some(message); }
        None
    }

    fn parse_unicode_braced_escape(&mut self) -> Option<String> {
        let mut idx = self.pos + 3;
        let mut digits = 0;
        let mut value: u32 = 0;
        loop {
            match self.units.get(idx).copied() {
                Some(0x7D) => break,
                Some(unit) if is_hex_digit(unit) => {
                    let digit = if unit <= 0x39 {
                        unit - 0x30
                    } else if unit <= 0x46 {
                        unit - 0x41 + 10
                    } else {
                        unit - 0x61 + 10
                    };
                    value = value.saturating_mul(16).saturating_add(u32::from(digit));
                    idx += 1;
                    digits += 1;
                    if digits > 6 {
                        return Some(format!("invalid regular expression"));
                    }
                }
                _ => return Some(format!("invalid regular expression")),
            }
        }
        if digits == 0 {
            return Some(format!("invalid regular expression"));
        }
        if value > 0x10FFFF || (0xD800..=0xDFFF).contains(&value) {
            return Some(format!("invalid regular expression"));
        }
        self.pos = idx + 1;
        if let Some(message) = self.skip_quantifier() { return Some(message); }
        None
    }

    fn parse_decimal_escape(&mut self) -> Option<String> {
        let mut idx = self.pos + 1;
        let mut value: usize = 0;
        while idx < self.units.len() {
            let unit = self.units[idx];
            if !(0x30..=0x39).contains(&unit) {
                break;
            }
            value = value.saturating_mul(10).saturating_add((unit - 0x30) as usize);
            idx += 1;
        }
        self.decimals.push(value);
        self.pos = idx;
        if let Some(message) = self.skip_quantifier() { return Some(message); }
        None
    }

    fn is_k_prefix(&self) -> bool {
        self.units.get(self.pos) == Some(&0x5C) && self.units.get(self.pos + 1) == Some(&0x6B)
    }

    fn parse_k_reference(&mut self) {
        self.pos += 2;
        if self.peek() != Some(0x3C) {
            self.bare_k += 1;
            return;
        }
        self.pos += 1;
        let name_start = self.pos;
        while let Some(unit) = self.peek() {
            if unit == 0x3E {
                break;
            }
            if unit == 0x29 || unit == 0x2F {
                break;
            }
            self.pos += 1;
        }
        if self.peek() != Some(0x3E) {
            self.incomplete_k += 1;
            return;
        }
        let name: Vec<u16> = self.units[name_start..self.pos].to_vec();
        self.references.push(name);
        self.pos += 1;
    }

    fn check_named_groups(&self) -> Option<String> {
        if let Some(message) = self.check_duplicate_groups() {
            return Some(message);
        }
        self.check_k_references()
    }

    fn check_duplicate_groups(&self) -> Option<String> {
        let mut idx = 0;
        while idx < self.groups.len() {
            let mut inner = idx + 1;
            while inner < self.groups.len() {
                if self.groups[idx].name == self.groups[inner].name
                    && can_both_participate(&self.groups[idx].context, &self.groups[inner].context)
                {
                    return Some(format!("invalid regular expression"));
                }
                inner += 1;
            }
            idx += 1;
        }
        None
    }

    fn check_k_references(&self) -> Option<String> {
        if matches!(self.mode, RegexMode::Unicode | RegexMode::UnicodeSets) {
            return self.check_k_strict();
        }
        if self.groups.is_empty() {
            return None;
        }
        self.check_k_strict()
    }

    fn check_k_strict(&self) -> Option<String> {
        if self.bare_k > 0 || self.incomplete_k > 0 {
            return Some(format!("invalid regular expression"));
        }
        for reference in &self.references {
            if reference.is_empty() {
                return Some(format!("invalid regular expression"));
            }
            if !self.groups.iter().any(|group| group.name == *reference) {
                return Some(format!("invalid regular expression"));
            }
        }
        None
    }

    fn check_decimals(&self) -> Option<String> {
        if !matches!(self.mode, RegexMode::Unicode | RegexMode::UnicodeSets) {
            return None;
        }
        for value in &self.decimals {
            if *value == 0 || *value > self.captures {
                return Some(format!("invalid regular expression"));
            }
        }
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

fn validate_group_name(name: &[u16]) -> Option<String> {
    let mut chars: Vec<char> = Vec::new();
    let mut idx = 0;
    while idx < name.len() {
        if let Some(message) = push_group_name_unit(name, &mut idx, &mut chars) {
            return Some(message);
        }
    }
    let mut chars = chars.iter();
    match chars.next() {
        Some(first) if is_id_start(*first) => {}
        _ => return Some(format!("invalid regular expression")),
    }
    if chars.any(|candidate| !is_id_continue(*candidate)) {
        return Some(format!("invalid regular expression"));
    }
    None
}

fn push_group_name_unit(name: &[u16], idx: &mut usize, chars: &mut Vec<char>) -> Option<String> {
    if name[*idx] == 0x5C {
        return push_group_name_escape(name, idx, chars);
    }
    if (0xD800..0xDC00).contains(&name[*idx])
        && *idx + 1 < name.len()
        && (0xDC00..0xE000).contains(&name[*idx + 1])
    {
        let high = u32::from(name[*idx] - 0xD800);
        let low = u32::from(name[*idx + 1] - 0xDC00);
        *idx += 2;
        return match char::from_u32(0x10000 + (high << 10) + low) {
            Some(candidate) => {
                chars.push(candidate);
                None
            }
            None => Some(format!("invalid regular expression")),
        };
    }
    if (0xD800..0xE000).contains(&name[*idx]) {
        return Some(format!("invalid regular expression"));
    }
    *idx += 1;
    match char::from_u32(u32::from(name[*idx - 1])) {
        Some(candidate) => {
            chars.push(candidate);
            None
        }
        None => Some(format!("invalid regular expression")),
    }
}

fn push_group_name_escape(name: &[u16], idx: &mut usize, chars: &mut Vec<char>) -> Option<String> {
    let Some(first) = decode_group_name_escape(name, idx) else {
        return Some(format!("invalid regular expression"));
    };
    if !(0xD800..0xDC00).contains(&first) {
        return match char::from_u32(first) {
            Some(candidate) => {
                chars.push(candidate);
                None
            }
            None => Some(format!("invalid regular expression")),
        };
    }
    let Some(second) = decode_group_name_escape(name, idx) else {
        return Some(format!("invalid regular expression"));
    };
    if !(0xDC00..0xE000).contains(&second) {
        return Some(format!("invalid regular expression"));
    }
    match char::from_u32(0x10000 + ((first - 0xD800) << 10) + (second - 0xDC00)) {
        Some(astral) => {
            chars.push(astral);
            None
        }
        None => Some(format!("invalid regular expression")),
    }
}

fn decode_group_name_escape(name: &[u16], idx: &mut usize) -> Option<u32> {
    if *name.get(*idx + 1)? != 0x75 {
        return None;
    }
    if *name.get(*idx + 2)? == 0x7B {
        let mut end = *idx + 3;
        while end < name.len() && name[end] != 0x7D {
            if !is_hex_digit(name[end]) {
                return None;
            }
            end += 1;
        }
        if end >= name.len() || end == *idx + 3 {
            return None;
        }
        let mut value: u32 = 0;
        for unit in &name[*idx + 3..end] {
            value = value * 16 + hex_value(*unit);
        }
        *idx = end + 1;
        Some(value)
    } else {
        let end = *idx + 6;
        if end > name.len() || name[*idx + 2..end].iter().any(|unit| !is_hex_digit(*unit)) {
            return None;
        }
        let mut value: u32 = 0;
        for unit in &name[*idx + 2..end] {
            value = value * 16 + hex_value(*unit);
        }
        *idx = end;
        Some(value)
    }
}

fn hex_value(unit: u16) -> u32 {
    match unit {
        0x30..=0x39 => u32::from(unit - 0x30),
        0x41..=0x46 => u32::from(unit - 0x41) + 10,
        _ => u32::from(unit - 0x61) + 10,
    }
}

fn can_both_participate(first: &[(usize, usize)], second: &[(usize, usize)]) -> bool {
    for (id, alt) in first {
        let mut idx = 0;
        while idx < second.len() {
            if &second[idx].0 == id && &second[idx].1 != alt {
                return false;
            }
            idx += 1;
        }
    }
    true
}

fn is_hex_digit(unit: u16) -> bool {
    matches!(unit, 0x30..=0x39 | 0x41..=0x46 | 0x61..=0x66)
}

fn is_braced_quantifier_at(units: &[u16], pos: usize) -> bool {
    let mut idx = pos + 1;
    let mut digits = 0;
    while idx < units.len() && (0x30..=0x39).contains(&units[idx]) {
        idx += 1;
        digits += 1;
    }
    if digits == 0 {
        return false;
    }
    if idx < units.len() && units[idx] == 0x2C {
        idx += 1;
        while idx < units.len() && (0x30..=0x39).contains(&units[idx]) {
            idx += 1;
        }
    }
    idx < units.len() && units[idx] == 0x7D
}

fn is_syntax_character(unit: u16) -> bool {
    matches!(
        unit,
        0x5E | 0x24 | 0x5C | 0x2E | 0x2A | 0x2B | 0x3F | 0x28 | 0x29 | 0x5B | 0x5D | 0x7B
            | 0x7D | 0x7C
    )
}

fn is_valid_u_single(escaped: u16, in_class: bool) -> bool {
    if matches!(
        escaped,
        0x64 | 0x44 | 0x77 | 0x57 | 0x73 | 0x53 | 0x62 | 0x42 | 0x66 | 0x6E | 0x72
            | 0x74 | 0x76
    ) {
        return true;
    }
    if is_syntax_character(escaped) || escaped == 0x2F {
        return true;
    }
    if in_class && escaped == 0x2D {
        return true;
    }
    false
}

fn is_v_single_error(unit: u16) -> bool {
    matches!(unit, 0x28 | 0x29 | 0x7B | 0x7D | 0x2F | 0x7C)
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
