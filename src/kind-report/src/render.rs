use std::collections::{HashMap, HashSet};

use std::fmt::{Display, Write};
use std::path::{Path, PathBuf};
use std::str;

use kind_span::{Pos, SyntaxCtxIndex};
use yansi::Paint;

use crate::{data::*, RenderConfig};

type SortedMarkers = HashMap<SyntaxCtxIndex, Vec<Marking>>;

#[derive(Debug, Clone)]
pub struct Point {
    pub line: usize,
    pub column: usize,
}

pub trait FileCache {
    fn fetch(&mut self, ctx: SyntaxCtxIndex) -> Option<&(PathBuf, String)>;
}

impl Display for Point {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}:{}", self.line + 1, self.column + 1)
    }
}

fn group_markers(markers: &[Marking]) -> SortedMarkers {
    let mut file_group = SortedMarkers::new();
    for marker in markers {
        let group = file_group.entry(marker.ctx).or_insert_with(Vec::new);
        group.push(marker.clone())
    }
    for group in file_group.values_mut() {
        group.sort_by(|x, y| x.position.start.cmp(&y.position.end));
    }
    file_group
}

pub fn get_code_line_guide(code: &str) -> Vec<usize> {
    let mut guide = Vec::new();
    let mut size = 0;
    for chr in code.chars() {
        size += chr.len_utf8();
        if chr == '\n' {
            guide.push(size);
        }
    }
    guide.push(code.len());
    guide
}

fn find_in_line_guide(pos: Pos, guide: &Vec<usize>) -> Point {
    for i in 0..guide.len() {
        if guide[i] > pos.index as usize {
            return Point {
                line: i,
                column: pos.index as usize - (if i == 0 { 0 } else { guide[i - 1] }),
            };
        }
    }
    Point {
        line: guide.len(),
        column: pos.index as usize,
    }
}

// Get color
pub fn get_colorizer<T>(color: &Color) -> &dyn Fn(T) -> Paint<T> {
    match color {
        Color::Fst => &|str| yansi::Paint::red(str).bold(),
        Color::Snd => &|str| yansi::Paint::blue(str).bold(),
        Color::Thr => &|str| yansi::Paint::green(str).bold(),
        Color::For => &|str| yansi::Paint::yellow(str).bold(),
        Color::Fft => &|str| yansi::Paint::cyan(str).bold(),
    }
}

// TODO: Remove common indentation.
// TODO: Prioritize inline marcations.
pub fn colorize_code<'a, T: Write + Sized>(markers: &mut [&(Point, Point, &Marking)], code_line: &'a str, fmt: &mut T) -> std::fmt::Result {
    markers.sort_by(|x, y| x.0.column.cmp(&y.0.column));
    let mut start = 0;
    for marker in markers {
        if start < marker.0.column {
            write!(fmt, "{}", &code_line[start..marker.0.column])?;
            start = marker.0.column;
        }

        let end = if marker.0.line == marker.1.line { marker.1.column } else { code_line.len() };

        if start < end {
            let colorizer = get_colorizer(&marker.2.color);
            write!(fmt, "{}", colorizer(&code_line[start..end]).bold())?;
            start = end;
        }
    }

    if start < code_line.len() {
        write!(fmt, "{}", &code_line[start..code_line.len()])?;
    }
    writeln!(fmt)?;
    Ok(())
}

pub fn paint_line<T>(data: T) -> Paint<T> {
    Paint::new(data).fg(yansi::Color::Cyan).dimmed()
}

pub fn mark_inlined<T: Write + Sized>(prefix: &str, config: &RenderConfig, inline_markers: &mut [&(Point, Point, &Marking)], fmt: &mut T) -> std::fmt::Result {
    inline_markers.sort_by(|x, y| x.0.column.cmp(&y.0.column));
    let mut start = 0;

    write!(fmt, "{:>5} {} {}", "", paint_line(config.chars.vbar), prefix)?;

    for marker in inline_markers.iter_mut() {
        if start < marker.0.column {
            write!(fmt, "{:pad$}", "", pad = marker.0.column - start)?;
            start = marker.0.column;
        }
        if start < marker.1.column {
            let colorizer = get_colorizer(&marker.2.color);
            write!(fmt, "{}", colorizer(config.chars.bxline.to_string()))?;
            write!(fmt, "{}", colorizer(config.chars.hbar.to_string().repeat((marker.1.column - start).saturating_sub(1))))?;
            start = marker.1.column;
        }
    }
    writeln!(fmt)?;
    for i in 0..inline_markers.len() {
        write!(fmt, "{:>5} {} {}", "", paint_line(config.chars.vbar), prefix)?;
        let mut start = 0;
        for j in 0..(inline_markers.len() - i) {
            let marker = inline_markers[j];
            if start < marker.0.column {
                write!(fmt, "{:pad$}", "", pad = marker.0.column - start)?;
                start = marker.0.column;
            }
            if start < marker.1.column {
                let colorizer = get_colorizer(&marker.2.color);
                if j == (inline_markers.len() - i).saturating_sub(1) {
                    write!(fmt, "{}", colorizer(format!("{} {}", config.chars.trline, marker.2.text)))?;
                } else {
                    write!(fmt, "{}", colorizer(config.chars.vbar.to_string()))?;
                }
                start += 1;
            }
        }
        writeln!(fmt)?;
    }
    Ok(())
}

pub fn write_code_block<'a, T: Write + Sized>(file_name: &Path, config: &RenderConfig, markers: &[Marking], group_code: &'a str, fmt: &mut T) -> std::fmt::Result {
    let guide = get_code_line_guide(group_code);

    let point = find_in_line_guide(markers[0].position.start, &guide);

    let header = format!(
        "{:>5} {}{}[{}:{}]",
        "",
        config.chars.brline,
        config.chars.hbar.to_string().repeat(2),
        file_name.to_str().unwrap(),
        point
    );

    writeln!(fmt, "{}", paint_line(header))?;

    writeln!(fmt, "{:>5} {}", "", paint_line(config.chars.vbar))?;

    let mut lines_set = HashSet::new();

    let mut markers_by_line: HashMap<usize, Vec<(Point, Point, &Marking)>> = HashMap::new();

    let mut multi_line_markers: Vec<(Point, Point, &Marking)> = Vec::new();

    for marker in markers {
        let start = find_in_line_guide(marker.position.start, &guide);
        let end = find_in_line_guide(marker.position.end, &guide);

        if let Some(row) = markers_by_line.get_mut(&start.line) {
            row.push((start.clone(), end.clone(), marker))
        } else {
            markers_by_line.insert(start.line, vec![(start.clone(), end.clone(), marker)]);
        }

        if end.line != start.line {
            multi_line_markers.push((start.clone(), end.clone(), marker));
        }

        if end.line - start.line <= 3 {
            for i in start.line..=end.line {
                lines_set.insert(i);
            }
        } else {
            lines_set.insert(start.line);
            lines_set.insert(end.line);
        }
    }

    let code_lines: Vec<&'a str> = group_code.lines().collect();
    let mut lines = lines_set.iter().collect::<Vec<&usize>>();
    lines.sort();

    for i in 0..lines.len() {
        let line = lines[i];
        let mut prefix = "   ".to_string();
        let mut empty_vec = Vec::new();
        let row = markers_by_line.get_mut(line).unwrap_or(&mut empty_vec);
        let mut inline_markers: Vec<&(Point, Point, &Marking)> = row.iter().filter(|x| x.0.line == x.1.line).collect();
        let mut current = None;

        for marker in &multi_line_markers {
            if marker.0.line == *line {
                prefix = format!(" {} ", get_colorizer(&marker.2.color)(config.chars.brline));
                current = Some(marker);
                break;
            } else if marker.1.line == *line || *line > marker.0.line && *line < marker.1.line {
                prefix = format!(" {} ", get_colorizer(&marker.2.color)(config.chars.vbar));
                current = Some(marker);
                break;
            }
        }

        write!(fmt, "{:>5} {} {}", line + 1, paint_line(config.chars.vbar), prefix,)?;

        if let Some(marker) = current {
            prefix = format!(" {} ", get_colorizer(&marker.2.color)(config.chars.vbar));
        }

        if !inline_markers.is_empty() {
            colorize_code(&mut inline_markers, code_lines[*line], fmt)?;
            mark_inlined(&prefix, config, &mut inline_markers, fmt)?;
        } else {
            writeln!(fmt, "{}", code_lines[*line])?;
        }

        if let Some(marker) = current {
            if marker.1.line == *line {
                let col = get_colorizer(&marker.2.color);
                writeln!(fmt, "{:>5} {} {} ", "", paint_line(config.chars.dbar), prefix)?;
                writeln!(
                    fmt,
                    "{:>5} {} {} ",
                    "",
                    paint_line(config.chars.dbar),
                    col(format!(" {} {}", config.chars.trline, marker.2.text))
                )?;
                prefix = "   ".to_string();
            }
        }

        if i < lines.len() - 1 && lines[i + 1] - line > 1 {
            writeln!(fmt, "{:>5} {} {} ", "", paint_line(config.chars.dbar), prefix)?;
        }
    }

    Ok(())
}

pub fn render_tag<T: Write + Sized>(severity: &Severity, fmt: &mut T) -> std::fmt::Result {
    match severity {
        Severity::Error => write!(fmt, " {} ", Paint::new(" ERROR ").bg(yansi::Color::Red).bold()),
        Severity::Warning => write!(fmt, " {} ", Paint::new(" WARN ").bg(yansi::Color::Yellow).bold()),
        Severity::Info => write!(fmt, " {} ", Paint::new(" INFO ").bg(yansi::Color::Blue).bold()),
    }
}

impl Diagnostic {
    pub fn render<T: Write + Sized, C: FileCache>(&self, cache: &mut C, config: &RenderConfig, fmt: &mut T) -> std::fmt::Result {
        writeln!(fmt)?;

        write!(fmt, " ")?;
        render_tag(&self.frame.severity, fmt)?;
        writeln!(fmt, "{}", Paint::new(&self.frame.title).bold())?;

        if !self.frame.subtitles.is_empty() {
            writeln!(fmt)?;
        }

        for subtitle in &self.frame.subtitles {
            match subtitle {
                Subtitle::Normal(color, phr) => {
                    let colorizer = get_colorizer(color);
                    writeln!(fmt, "{:>5} {} {}", "", colorizer("•"), Paint::new(phr).bold())?;
                }
                Subtitle::Phrase(color, words) => {
                    let colorizer = get_colorizer(color);
                    write!(fmt, "{:>5} {} ", "", colorizer("•"))?;
                    for word in words {
                        match word {
                            Word::White(str) => write!(fmt, "{} ", Paint::new(str).bold())?,
                            Word::Painted(color, str) => {
                                let colorizer = get_colorizer(color);
                                write!(fmt, "{} ", colorizer(str))?
                            }
                        }
                    }
                    writeln!(fmt)?;
                }
            }
        }

        let groups = group_markers(&self.frame.positions);

        for (ctx, group) in groups {
            writeln!(fmt)?;
            let (file, code) = cache.fetch(ctx).unwrap();
            write_code_block(file, config, &group, code, fmt)?;
        }

        writeln!(fmt)?;

        for hint in &self.frame.hints {
            writeln!(
                fmt,
                "{:>5} {} {}",
                "",
                Paint::new("Hint:").fg(yansi::Color::Cyan).bold(),
                Paint::new(hint).fg(yansi::Color::Cyan)
            )?;
        }

        Ok(())
    }
}