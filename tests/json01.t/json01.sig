UserAddress { city: string }

User { sessionId: string, name: string, address: UserAddress }

event Request { method: string, url: string, user: User }
event Report { reason: string, user: User}