use std::path::Path;
use std::process::exit;
use std::{env, fs};

fn main() {
    let args: Vec<String> = env::args().collect();

    if args.len() <= 2 {
        return;
    }

    let file_path = &args[1];

    let path = Path::new(file_path);
    if !path.exists() {
        eprintln!("ERROR: The file '{}' does not exist.", file_path);
        exit(1);
    }

    if !path.is_file() {
        eprintln!("ERROR: '{}' is not a file.", file_path);
        exit(1);
    }

    let content = match fs::read_to_string(file_path) {
        Ok(text) => text,
        Err(e) => {
            eprintln!("ERROR: {}", e);
            exit(1);
        }
    };

    let formatted = format_content(&content);

    let action = &args[2];

    if action == "--print" {
        print!("{}", formatted);
    }
}

fn format_content(content: &str) -> String {
    let mut result = String::new();
    let mut lines = content.lines();

    while let Some(line) = lines.next() {
        let trimmed_line = trim_whitespace(line);
        let line_with_dot_replaced = replace_leading_dot_with_middle_dot(&trimmed_line);
        let formatted_line = format_spaces(&line_with_dot_replaced);
        result.push_str(&formatted_line);

        if lines.clone().next().is_some() {
            result.push('\n');
        }
    }

    result.replace('$', "<|")
}

fn split_leading_whitespace(s: &str) -> (&str, &str) {
    let trimmed = s.trim_start();
    let pos = s.len() - trimmed.len();
    s.split_at(pos)
}

fn replace_leading_dot_with_middle_dot(line: &str) -> String {
    let (indent, content) = split_leading_whitespace(line);

    if let Some(suffix) = content.strip_prefix('.') {
        let mut result = String::with_capacity(line.len());

        result.push_str(indent);
        result.push('·');
        result.push_str(suffix);

        result
    } else {
        line.to_string()
    }
}

fn format_spaces(line: &str) -> String {
    let mut result = String::new();
    let (indent, content) = split_leading_whitespace(line);
    let mut chars = content.chars().peekable();

    let mut space_needed: bool = false;

    result.push_str(indent);

    while let Some(c) = chars.next() {
        if space_needed {
            result.push(' ');
        }
        space_needed = false;

        match c {
            '(' | ' ' => {
                while let Some(&next_c) = chars.peek() {
                    if next_c == ' ' {
                        chars.next();
                    } else {
                        break;
                    }
                }
            }
            ')' | ';' | ',' => {
                while result.ends_with(' ') {
                    result.pop();
                }
            }
            ':' => {
                while result.ends_with(' ') {
                    result.pop();
                }
                result.push(' ');
                while let Some(&next_c) = chars.peek() {
                    if next_c == ' ' {
                        chars.next();
                    } else if next_c == '=' {
                        break;
                    } else {
                        space_needed = true;
                        break;
                    }
                }
            }
            _ => (),
        };
        result.push(c)
    }

    result
}

fn trim_whitespace(line: &str) -> String {
    let trimmed_end = line.trim_end();

    let (whitespace, content) = split_leading_whitespace(trimmed_end);

    let adjusted_whitespace = if whitespace.len() % 2 == 1 && !whitespace.is_empty() {
        &whitespace[0..whitespace.len() - 1]
    } else {
        whitespace
    };

    format!("{}{}", adjusted_whitespace, content)
}
