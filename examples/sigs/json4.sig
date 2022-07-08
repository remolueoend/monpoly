LogMeta {
	code: int
}

LogData {
	message: string,
	meta: LogMeta
}

event Log {
	data: LogData
}