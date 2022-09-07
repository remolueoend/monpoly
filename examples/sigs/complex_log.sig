
LogEntry {
	level: string,
	time: string,
	message: string,
	module: string,
	line: int,
	host: string
}

event Log {
	type: string,
	event: {
		src: {a: int},
		log_entry: LogEntry
	}
}

