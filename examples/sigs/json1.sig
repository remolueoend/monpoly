User { sessionId: string, name: string, address: {city: string} }

event Request { method: string, url: string, user: User }
event Report { user: User, reason: string }