LogEventSource {a: int}
LogEntry {level: string, time: string, message: string, module: string, line: int, host: string}
LogEvent {src: LogEventSource, log_entry: LogEntry}
Log {type: string, event: LogEvent}